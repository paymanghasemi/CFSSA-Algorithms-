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

IloNumVarArray Intersection_variable(env);

IloModel Intersection_model(env);
IloObjective Intersection_Obj(env);
IloCplex Intersection_Cplex(Intersection_model);
IloRangeArray Intersection_constraints(env);

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
    Y = new double [N_Objectives];
    Y_cut = new double [N_Objectives];
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


    Intersection_variable = IloNumVarArray(env, N_Objectives, 0.0, +IloInfinity, ILOFLOAT);
    Intersection_Obj = IloMaximize(env, Intersection_variable[0]);
    Intersection_model.add(Intersection_Obj);
}

void WSO2() {
    run_start = clock();
    counter++;
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
        if (Global_UB > UB) {
            Global_UB = UB;
        }
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
    } else if(status!= CPX_STAT_ABORT_TIME_LIM) {
        Infeasible = 1;
        if(counter==1){
            cout<<"Problem is infeasible"<<endl;
            WSO_done = 1;
        }else{
            WSO_done = 1;
            Global_UB=Global_LB;
        }
    }

    if (Infeasible == 0 && LB > Global_LB) {

        Global_LB = LB;
        for (int i = 0; i < N_Objectives; i++) {
            Y_star[i] = Y[i];
        }
        Math.clear();
        for (int i = 0; i < N_Objectives; i++) {
            Math += (W[i] * ObjF[i] / Y[i]);
        }
        Model.add(Math - Check_RHS >= 0);
        Math.clear();
    } else if (Infeasible == 0 && LB > epsilon) {
        Math.clear();
        for (int i = 0; i < N_Objectives; i++) {
            Math += (W[i] * ObjF[i] / Y[i]);
        }
        Model.add(Math - Check_RHS >= 0);
        Math.clear();
    } else if (Infeasible == 1) {
        WSO_done = 1;
        Global_UB = Global_LB;
    }
    run_time = clock() - run_start;
    run_time = run_time / CLOCKS_PER_SEC;
    T_limit -= run_time;
    if (T_limit < 0) {
        T_limit = 0;
    }
}

void Algorithm() {
        while(!WSO_done && T_limit>0 && Global_UB > Global_LB + Abs_Optimal_Tol && (Global_UB - Global_LB) / (Global_UB + denominator) > Rel_Optimal_Tol){
            WSO2();
        }
        if (Global_UB <= Global_LB + Abs_Optimal_Tol || (Global_UB - Global_LB) / (Global_UB + denominator) <= Rel_Optimal_Tol) {
                Global_UB = Global_LB;
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
    T_limit = Time_Limit;
    Reading_LP_File_and_Generating_CPLEX_Variables();
    Global_LB = 0;
    Global_UB = Positive_infinity;
    
    counter = 0;
    Cplex.setOut(env.getNullStream());
    
    gettimeofday(&startTime, NULL);
    
    if(tune_lvl!=0){
        tune_start_time = clock();
    Cplex.setParam(IloCplex::Threads, Num_threads);
    Cplex.setParam(IloCplex::TiLim, N_Variables-N_Objectives);
    Cplex.setParam(IloCplex::TuningTiLim, 0.25*(N_Variables-N_Objectives));
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
    gettimeofday(&startTime, NULL);
    Algorithm();
    
    gettimeofday(&endTime, NULL);
    clock_Run_time += (clock() - clock_start_time);
    clock_Run_time /= CLOCKS_PER_SEC;
    Writing_Output();
    return 0;
}
