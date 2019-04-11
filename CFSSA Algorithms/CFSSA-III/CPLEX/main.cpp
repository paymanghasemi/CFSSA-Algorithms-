/* 
 * File:   main.cpp
 * Author: c3156840
 */

#include <cstdlib>
#include <iostream>
#include <fstream>
#include <ilcplex/ilocplex.h>
#include <sys/time.h>
#include <ctime>
#include <math.h>   
#include <vector>

using namespace std;

/*------------------------------------------------------------------------------
 
 -----------------------------Public Variables----------------------------------
 
 -----------------------------------------------------------------------------*/
#define Output_Precision 20
#define CPLEX_Relative_Gap 1.0e-6
#define Num_threads 1 
#define Time_Limit 3600 
#define Negative_infinity -1000000
#define Positive_infinity 1000000
#define epsilon 1.0e-6
#define Abs_Optimal_Tol 1.0e-6
#define Rel_Optimal_Tol 1.0e-6
#define denominator 1.0e-12


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
double run_start = 0;
double run_time = 0;
double T_limit = 0;

double* Y_star;
double Nodes_explored = 0;
double Nodes_proned = 0;
double Nodes_infeasible = 0;
double Global_LB;
double Global_UB;
double N_LP = 0;
double Check_RHS;
double Nodes_N_added = 0;
double status;
int* W;
int Total_W(0);
/*------------------------------------------------------------------------------
 
 ------------------------Declaring CPLEX information----------------------------
 
 -----------------------------------------------------------------------------*/
ILOSTLBEGIN
IloEnv env;
IloModel Model(env);
IloObjective Objective(env);
IloRangeArray Constraints(env);
IloSOS1Array sos1(env);
IloSOS2Array sos2(env);
IloNumVarArray Variable(env);
IloExprArray ObjF(env);
IloCplex Cplex(Model);
IloRangeArray Cuts(env);
IloRangeArray Tabulist(env);
IloRangeArray Bounds(env);
IloExpr Math(env);

IloObjective Check_Objective(env);

/*------------------------------------------------------------------------------
 
 ------------------------------------Functions-----------------------------------
 
 -----------------------------------------------------------------------------*/


void Reading_LP_File_and_Generating_CPLEX_Variables() {
    Cplex.importModel(Model, IP_file_name, Objective, Variable, Constraints, sos1, sos2);
    sos1.clear();
    sos1.end();
    sos2.clear();
    sos2.end();
    Model.remove(Objective);
    N_Variables = Variable.getSize();
    ObjF.end();
    ObjF = IloExprArray(env, N_Objectives);
    Y_star = new double [N_Objectives];
    Model.remove(Constraints);
    for (int i = 0; i < N_Objectives; i++) {
        Y_star[i] = 0;
        ObjF[i] = Constraints[0].getExpr();
        Constraints.remove(0);
    }
    N_Constraints = Constraints.getSize() - N_Objectives;
    Model.add(Constraints);
    Math.clear();
    for (int i = 0; i < N_Objectives; i++) {
        Math += W[i] * ObjF[i];
    }
    Objective = IloMaximize(env, Math);
    Model.add(Objective);
    Check_RHS = Total_W;
}

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
            LB_for_Obj[i] = Negative_infinity;
        }
        Do_Branch = 0;
    }

    void Reinitializing_The_Node(Node* Parent, int identifier) {
        for (int i = 0; i < N_Objectives; i++) {
            LB_for_Obj[i] = Parent->LB_for_Obj[i];
        }
        Identifier = identifier;
        LB_for_Obj[Identifier] = Parent->Y[Identifier];
        UB = Parent->UB;
    }

    void Node_Explore() {
        run_start = clock();
        Nodes_explored++;
        Bounds.clear();
        for (int i = 0; i < N_Objectives; i++) {
            Bounds.add(ObjF[i] >= LB_for_Obj[i] - epsilon);
        }
        Model.add(Bounds);
        
        Cplex.extract(Model);
        Cplex.setParam(IloCplex::TiLim, T_limit);
        N_LP++;
        Cplex.solve();
        status = Cplex.getCplexStatus();
        if (status == CPX_STAT_OPTIMAL) {
            Objective_value = Cplex.getObjValue();
            LB = 1;
            for (int i = 0; i < N_Objectives; i++) {
                Y[i] = Cplex.getValue(ObjF[i]);
                LB *= pow(Y[i], W[i]);
            }
            UB = Objective_value / Total_W;
            UB = pow(UB, Total_W);
            Math.clear();
            for (int i = N_Objectives; i < N_Variables; i++) {
                if (Cplex.getValue(Variable[i]) >= 1 - epsilon) {
                    Math += (1 - Variable[i]);
                } else {
                    Math += Variable[i];
                }
            }
            Model.add(Math >= 1);
            Math.clear();
            if (LB > epsilon) {
                Math.clear();
                for (int i = 0; i < N_Objectives; i++) {
                    Math += (W[i] * ObjF[i] / Y[i]);
                }
                Model.add(Math - Check_RHS >= 0);
                Math.clear();
                if (LB > Global_LB) {
                    Global_LB = LB;
                    for (int i = 0; i < N_Objectives; i++) {
                        Y_star[i] = Y[i];
                    }
                }
            }
            Do_Branch = 1;
        } else if (status != CPX_STAT_ABORT_TIME_LIM) {
            Nodes_infeasible++;
        }

        Model.remove(Bounds);
        Bounds.clear();

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

void Writing_Output() {
    ofstream OutputFile;
    OutputFile.open("Results.txt", ios::app);
    OutputFile << IP_file_name << " GLB= " << std::setprecision(Output_Precision) << Global_LB << " GUB= " << Global_UB << " Gap= " << (Global_UB - Global_LB) / Global_UB << " #VAR= " << N_Variables - N_Objectives << " #Const= " << N_Constraints << " Time= " << (clock_Run_time / CLOCKS_PER_SEC) << " Open= " << Tree_of_Nodes.size() << " Explored= " << Nodes_explored << " Inf= " << Nodes_infeasible << " Pruned= " << Nodes_proned << " #IP= " << N_LP << " tune= " << tune_Run_time << endl;
    OutputFile.close();
}

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
            Tree_of_Nodes.push_back(New_Node[j]);
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

int main(int argc, char *argv[]) {
    //---------------------------Preparation Phase------------------------------
    IP_file_name = argv[1];
    int tune_lvl = atoi(argv[2]);
    N_Objectives = atoi(argv[3]);
    W = new int [N_Objectives];
    for (int i = 0; i < N_Objectives; i++) {
        W[i] = atoi(argv[i + 4]);
        Total_W += W[i];
    }

    T_limit = Time_Limit;
    Reading_LP_File_and_Generating_CPLEX_Variables();
    Global_LB = Negative_infinity;
    Global_UB = Positive_infinity;
    Cplex.setOut(env.getNullStream());
    gettimeofday(&startTime, NULL);


    if (tune_lvl != 0) {
        tune_start_time = clock();
        Cplex.setParam(IloCplex::Threads, Num_threads);
        Cplex.setParam(IloCplex::TiLim, N_Variables - N_Objectives);
        Cplex.setParam(IloCplex::TuningTiLim, 0.25 * (N_Variables - N_Objectives));
        IloCplex::ParameterSet fixedset(env);
        fixedset = Cplex.getParameterSet();
        Cplex.extract(Model);

        Cplex.tuneParam(fixedset);
        Cplex.writeParam("tune.prm");
        tune_Run_time = clock() - tune_start_time;
        tune_Run_time /= CLOCKS_PER_SEC;
    }

    Cplex.setParam(IloCplex::Threads, Num_threads);
    Cplex.setParam(IloCplex::EpGap, CPLEX_Relative_Gap);

    clock_start_time = clock();

    Node* Initial_Node = new Node;
    Tree_of_Nodes.push_back(Initial_Node);
    Branch_and_bound();

    gettimeofday(&endTime, NULL);
    clock_Run_time += (clock() - clock_start_time);
    Writing_Output();
    return 0;
}

