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
double run_start = 0;
double run_time = 0;
double T_limit = 0;

double* Y_star;
double* Y;
double* Y_cut;
double LB;
double UB;
double Global_LB;
double Global_UB;
double N_LP = 0;
double Check_RHS;
double Objective_value;
int* W;
int Total_W(0);
bool Infeasible = 0;
int counter;
bool Search_done = 0;
double Check_Value;
bool WSO_done = 0;

double tune_Run_time(0);
double tune_start_time;
int status;
double* Variable_value;
int intersection_constraint_size;
GRBEnv env;
GRBModel* Model;
GRBVar *Variable;
GRBLinExpr *ObjF;
GRBConstr *Bounds;
GRBLinExpr Objective;
GRBLinExpr Math;

//GRBModel* Model2;


void Check_Cutting_Plane() {
    Check_Value = 0;
    Math.clear();
    for (int i = 0; i < N_Objectives; i++) {
        Math += (W[i] / Y[i]) * ObjF[i];
    }
    Model->setObjective(Math, GRB_MAXIMIZE);
    Math.clear();
    Model->set(GRB_DoubleParam_TimeLimit, T_limit);
    N_LP++;
    Model->optimize();
    status = Model->get(GRB_IntAttr_Status);
    if (status == GRB_OPTIMAL) {
        Check_Value = Model->get(GRB_DoubleAttr_ObjVal);
        if (Check_Value > Check_RHS) {
            LB = 1;
            Variable_value = Model->get(GRB_DoubleAttr_X, Model->getVars(), N_Variables);
            for (int i = 0; i < N_Objectives; i++) {
                Y[i] = Variable_value[i];
                LB *= pow(Y[i], W[i]);
            }
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
            if (LB > epsilon) {
                Math.clear();
                for (int i = 0; i < N_Objectives; i++) {
                    Math += (W[i] / Y[i]) * ObjF[i];
                }
                Model->addConstr(Math >= Check_RHS);
                Math.clear();
                if (LB > Global_LB) {
                    Global_LB = LB;
                    for (int i = 0; i < N_Objectives; i++) {
                        Y_star[i] = Y[i];
                    }
                }
            }
        }else{
            Search_done=1;
            Global_UB = Global_LB;
        }
    }else if (status != GRB_TIME_LIMIT) {
        Search_done=1;
        Global_UB = Global_LB;
    }
    Model->setObjective(Objective,GRB_MAXIMIZE);
}

void WSO() {
    run_start = clock();
    counter++;
    Model->set(GRB_DoubleParam_TimeLimit, T_limit);
    N_LP++;
    Model->optimize();
    status = Model->get(GRB_IntAttr_Status);
    if (status == GRB_OPTIMAL) {
        Objective_value = Model->get(GRB_DoubleAttr_ObjVal);
        LB = 1;
        Variable_value = Model->get(GRB_DoubleAttr_X,Model->getVars(),N_Variables);
        for(int i=0; i<N_Objectives; i++){
                Y[i]= Variable_value[i];
                LB *= pow(Y[i],W[i]);
            }
        UB = Objective_value / Total_W;
        UB = pow(UB, Total_W);
        if(Global_UB> UB){
            Global_UB = UB;
        }
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
    } else if(status!=GRB_TIME_LIMIT) {
        Infeasible = 1;
        Search_done = 1;
        if(counter==1){
            cout<<"Problem is infeasible"<<endl;           
        }else{
            Global_UB=Global_LB;
        }
    }
    run_time = clock() - run_start;
    run_time = run_time / CLOCKS_PER_SEC;
    T_limit -= run_time;
    if (T_limit < 0) {
        T_limit = 0;
    }
    run_start = clock();   
    if (Infeasible == 0 && LB > epsilon) {
        Math.clear();
        for (int i = 0; i < N_Objectives; i++) {
            Math += (W[i] / Y[i]) * ObjF[i];
        }
        Model->addConstr(Math >= Check_RHS);
        Math.clear();
        if (LB > Global_LB) {
            Global_LB = LB;
            for (int i = 0; i < N_Objectives; i++) {
                Y_star[i] = Y[i];
            }
        }
        Check_Cutting_Plane();
    }
    run_time = clock() - run_start;
    run_time = run_time / CLOCKS_PER_SEC;
    T_limit -= run_time;
    if (T_limit < 0) {
        T_limit = 0;
    }

}


void Algorithm() {
    Global_LB = 0;
    Global_UB = Positive_infinity;
    counter = 0;
    Search_done=0;
    while(!Search_done && T_limit>0 && Global_UB > Global_LB + Abs_Optimal_Tol && (Global_UB - Global_LB) / (Global_UB + denominator) > Rel_Optimal_Tol){
    WSO();}

    if(Global_UB <= Global_LB + Abs_Optimal_Tol || (Global_UB - Global_LB) / (Global_UB + denominator) <= Rel_Optimal_Tol){
                Global_UB=Global_LB;
            }
}


void Writing_Output(){
    ofstream OutputFile;
    OutputFile.open("Results.txt", ios::app);
    OutputFile<<IP_file_name<<" GLB= "<< std::setprecision(Output_Precision) << Global_LB<< " GUB= "<< Global_UB<<" Gap= "<< (Global_UB-Global_LB)/Global_UB << " #VAR= "<< N_Variables - N_Objectives << " #Const= "<< N_Constraints<< " Time= "<< clock_Run_time<<" #IP= "<<N_LP<<" tune= "<<tune_Run_time<<endl;
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
    Y_star = new double [N_Objectives];
    Y = new double [N_Objectives];
    Y_cut = new double [N_Objectives];
    for(int i=0; i<N_Objectives;i++){
        Y_star[i] = 0;
        ObjF[i].clear();
        ObjF[i]=Variable[i];
        Objective += W[i]*ObjF[i];
        Model->remove(Model->getConstrs()[i]);
    }
    Check_RHS=Total_W;
    T_limit = Time_Limit;
    
    gettimeofday(&startTime, NULL);
    
    
    if(tune_lvl !=0){
        tune_start_time=clock();
    Model->setObjective(Objective,GRB_MAXIMIZE); 
    Model->set(GRB_IntParam_Threads, Num_threads);
    Model->set(GRB_DoubleParam_TuneTimeLimit, N_Variables-N_Objectives);
    Model->tune();
    Model->getTuneResult(0);
    Model->write("tune.prm");
    tune_Run_time = clock() - tune_start_time;
    tune_Run_time /= CLOCKS_PER_SEC;   
    }
    
    
    
    
    Model->set(GRB_IntParam_OutputFlag,0);
    Model->set(GRB_IntParam_Threads, Num_threads);
    Model->set(GRB_DoubleParam_MIPGap, Relative_Gap);
    Model->set(GRB_DoubleParam_MIPGapAbs, Relative_Gap);
    Model->setObjective(Objective,GRB_MAXIMIZE);
    
    
    clock_start_time = clock();
        
    Algorithm();
        
    gettimeofday(&endTime, NULL);
    clock_Run_time += (clock() - clock_start_time);
    clock_Run_time /= CLOCKS_PER_SEC;
    Writing_Output();
  return 0;
}