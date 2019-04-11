/* Copyright 2018, Gurobi Optimization, LLC */

/* Want to cover three different sets but subject to a common budget of
 * elements allowed to be used. However, the sets have different priorities to
 * be covered; and we tackle this by using multi-objective optimization. */

#include "gurobi_c++.h"
#include <cstdlib>
#include <iostream>
#include <fstream>
#include <sys/time.h>
#include <ctime>
#include <math.h>
#include <unistd.h>
#include <iomanip>  

using namespace std;

#define Output_Precision 20
#define Relative_Gap 1.0e-6
#define Num_threads 1 
#define denominator 1.0e-12
#define Time_Limit 3600 
#define Negative_infinity -1000000
#define Positive_infinity 1000000
#define epsilon 1.0e-6
#define Abs_Optimal_Tol 1.0e-6
#define Rel_Optimal_Tol 1.0e-6


char* IP_file_name;
int N_Variables;
int N_Objectives;
int N_Constraints;
struct timeval startTime, endTime;
double totalTime(0);
double clock_Run_time(0);
double clock_start_time;

double tune_Run_time(0);
double tune_start_time;

double run_start=0;
double run_time=0;
double T_limit=0;

double Nodes_explored=0;
double Nodes_proned=0;
double Nodes_infeasible=0;
double Global_LB;
double Global_UB;
double N_LP=0;
double Check_RHS;
double Nodes_N_added=0;
int status;
int* W;
int Total_W(0);
double Temp_RHS;
double* Variable_value;


GRBEnv env;
GRBModel* Model;
GRBVar *Variable;
GRBLinExpr *ObjF;
GRBConstr *Bounds;
GRBLinExpr Objective;
GRBLinExpr Math;
//GRBModel* Model2;

class Node {
public:

    double* Y;
    double Objective_value;
    double* LB_for_Obj;
    double UB;
    double LB;
    int Identifier;
    bool Do_Branch;

    


    Node() {
        LB_for_Obj = new double [N_Objectives];
        Y = new double [N_Objectives];
        for (int i = 0; i < N_Objectives; i++) {
            LB_for_Obj[i] = 0.0;
        }
        Do_Branch = 0;
    }

    void Reinitializing_The_Node(Node* Parent, int identifier) {
        for (int i = 0; i < N_Objectives; i++) {
            LB_for_Obj[i] = Parent->LB_for_Obj[i];
        }
        Identifier = identifier;
        LB_for_Obj[Identifier] = Parent->Y[Identifier];
        UB= Parent->UB;
    }


    
    void Node_Explore(){
        run_start = clock();
        Nodes_explored++;
        
        for (int i = 0; i < N_Objectives; i++) {
            Bounds[i] = Model->addConstr(Variable[i] >= LB_for_Obj[i] - epsilon);
        }     
        Model->set(GRB_DoubleParam_TimeLimit, T_limit);
        N_LP++;        
        Model->optimize();
        status = Model->get(GRB_IntAttr_Status);
        if (status == GRB_OPTIMAL) {
            Objective_value = Model->get(GRB_DoubleAttr_ObjVal);
            Variable_value = Model->get(GRB_DoubleAttr_X,Model->getVars(),N_Variables);
            LB=1;
            for(int i=0; i<N_Objectives; i++){
                Y[i]= Variable_value[i];
                LB *= pow(Y[i],W[i]);
            }
            UB= Objective_value/Total_W;
            UB= pow(UB, Total_W);
            Math.clear();
            for (int i = N_Objectives; i < N_Variables; i++) {
                if (Variable_value[i] >= 1 - epsilon) {
                    Math += (1 - Variable[i]);
                } else {
                    Math += Variable[i];
                }
            }
            Model->addConstr(Math >= 1);
            Math.clear();
            if ( LB > epsilon) {
                Math.clear();
                for (int i = 0; i < N_Objectives; i++) {
                    Math += (W[i] / Y[i]) * ObjF[i];
                }
                Model->addConstr(Math >= Check_RHS);
                Math.clear();
                if (LB > Global_LB) {
                    Global_LB = LB;
//                    for (int i = 0; i < N_Objectives; i++) {
//                        Y_star[i] = Y[i];
//                    }
                }
            }
            Do_Branch=1;
        } else if(status!= GRB_TIME_LIMIT){
            Nodes_infeasible++;}
        
        for (int i = 0; i < N_Objectives; i++) {
            Model->remove(Bounds[i]);
        }
        run_time = clock() - run_start;
        run_time = run_time / CLOCKS_PER_SEC;
        T_limit -= run_time;
        if (T_limit < 0) {
            T_limit = 0;
        }
    }
       

    
    virtual ~Node() {
        delete [] LB_for_Obj;
        delete [] Y;
    }
};

vector <Node*>Tree_of_Nodes;




void Add_The_Node_To_Tree(Node* New_Generated_Node) {
    run_start = clock();
    Node * New_Node[N_Objectives];

        //*********//
        for (int i = 0; i < N_Objectives; i++) {
            New_Node[i] = new Node;
            New_Node[i]->Reinitializing_The_Node(New_Generated_Node, i);
        }
    
    
    bool It_is_Added = 0;
    for (int i = 1; i < Tree_of_Nodes.size(); i++) {
        if (New_Generated_Node->UB > Tree_of_Nodes.at(i)->UB + epsilon) {
            for (int j = 0; j < N_Objectives; j++) {
                Tree_of_Nodes.insert(Tree_of_Nodes.begin() + i, New_Node[j]);
        }
            
            It_is_Added = 1;
            break;
        }
    }
    if (It_is_Added == 0) {
        for (int j = 0; j < N_Objectives; j++) {
                Tree_of_Nodes.push_back( New_Node[j]);
        }
    }
    run_time = clock() - run_start;
    run_time = run_time / CLOCKS_PER_SEC;
    T_limit -= run_time;
    if (T_limit < 0) {
        T_limit = 0;
    }
}

void Branch_and_bound() {
    while (T_limit > 0 && Tree_of_Nodes.size() > 0 && (Global_UB > Global_LB + Abs_Optimal_Tol) && (Global_UB - Global_LB) / (Global_UB + denominator) > Rel_Optimal_Tol) {
        Tree_of_Nodes.front()-> Node_Explore();
            if (Tree_of_Nodes.front()->Do_Branch == 1 && (Tree_of_Nodes.front()->UB > Global_LB + Abs_Optimal_Tol) && (Tree_of_Nodes.front()->UB - Global_LB) / (Tree_of_Nodes.front()->UB + denominator) > Rel_Optimal_Tol) {
                Add_The_Node_To_Tree(Tree_of_Nodes.front());
            } else if (Tree_of_Nodes.front()->Do_Branch == 1) {
                Nodes_proned++;
            }
        Tree_of_Nodes.front()->~Node();
        Tree_of_Nodes.erase(Tree_of_Nodes.begin());
        Global_UB = Tree_of_Nodes.front()->UB;

        if (T_limit > epsilon && (Global_UB <= Global_LB + Abs_Optimal_Tol || Tree_of_Nodes.size() == 0 || (Global_UB - Global_LB) / (Global_UB + denominator) <= Rel_Optimal_Tol)) {
            Global_UB = Global_LB;
        }
    }
}

void Writing_Output(){
    ofstream OutputFile;
    OutputFile.open("Results.txt", ios::app);
    OutputFile<<IP_file_name<<" GLB= "<< std::setprecision(Output_Precision) << Global_LB<< " GUB= "<< Global_UB<<" Gap= "<< (Global_UB-Global_LB)/Global_UB << " #VAR= "<< N_Variables - N_Objectives << " #Const= "<< N_Constraints<< " Time= "<< clock_Run_time<<" Open= "<<Tree_of_Nodes.size()<<" Explored= "<<Nodes_explored<<" Inf= "<<Nodes_infeasible<<" Pruned= "<<Nodes_proned<<" #IP= "<<N_LP<<" tune= "<<tune_Run_time<<endl;
    OutputFile.close();
}

int main(int argc, char *argv[]) {
    
    IP_file_name = argv[1];
    int tune_lvl = atoi(argv[2]);
    N_Objectives = atoi(argv[3]);
    W= new int [N_Objectives];
    for(int i=0; i< N_Objectives; i++){
        W[i]= atoi(argv[i+4]);
        Total_W += W[i];
    }
    
    env.set(GRB_IntParam_OutputFlag,0);
    Model = new GRBModel(env, IP_file_name);
    Model->set(GRB_IntParam_UpdateMode, 1);
    Variable= Model->getVars();
    Bounds = new GRBConstr [N_Objectives];
    N_Variables= Model->get(GRB_IntAttr_NumVars);
    N_Constraints= Model->get(GRB_IntAttr_NumConstrs);
    ObjF = new GRBLinExpr [N_Objectives];
    Objective.clear();
    for(int i=0; i<N_Objectives;i++){
        ObjF[i].clear();
        ObjF[i]=Variable[i];
        Objective += W[i]*ObjF[i];
        Model->remove(Model->getConstrs()[i]);
    }
    Check_RHS=Total_W;
    T_limit = Time_Limit;
    Global_LB = Negative_infinity;
    Global_UB = Positive_infinity;
    
    gettimeofday(&startTime, NULL);
    
    
    if(tune_lvl !=0){
        tune_start_time=clock();
    Model->setObjective(Objective,GRB_MAXIMIZE); 
    Model->set(GRB_IntParam_Threads, Num_threads);
    Model->set(GRB_DoubleParam_TimeLimit, T_limit);
    Model->tune();
    Model->getTuneResult(0);
    Model->write("tune.prm");
    tune_Run_time = clock() - tune_start_time;
    tune_Run_time /= CLOCKS_PER_SEC;
    
    
    }
    
    
    
    Model->setObjective(Objective,GRB_MAXIMIZE);
    Model->set(GRB_IntParam_OutputFlag,0);
    Model->set(GRB_IntParam_UpdateMode, 1);
    Model->set(GRB_IntParam_Threads, Num_threads);
    Model->set(GRB_DoubleParam_MIPGap, Relative_Gap);
    
    clock_start_time = clock();
        
        Node* Initial_Node = new Node;
        Tree_of_Nodes.push_back(Initial_Node);
        Branch_and_bound();
        
    gettimeofday(&endTime, NULL);
    clock_Run_time += (clock() - clock_start_time);
    clock_Run_time /= CLOCKS_PER_SEC;
    Writing_Output();
  return 0;
}
