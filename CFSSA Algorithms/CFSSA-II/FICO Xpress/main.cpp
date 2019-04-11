/********************************************************
  Xpress-BCL C++ Example Problems
  ===============================

  file xbworkrng.cxx
  ``````````````````
  Workshop planning example.
  Test ranges and number printing format.

  (c) 2008 Fair Isaac Corporation
      author: S.Heipcke, 2003, rev. Mar. 2011
********************************************************/



#include <cstdlib>
#include <iostream>
#include <fstream>
#include <sys/time.h>
#include <ctime>
#include <math.h>
#include <unistd.h>
#include <iomanip>
#include <vector>
#include "xprb_cpp.h"
#include "xprs.h"
#include "xprs_mse_defaulthandler.h"

using namespace std;
using namespace dashoptimization;



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


char* Problem;
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


double Temp_RHS;
double** Matrix_obj;
double** Matrix_contraint;
int tuner_lvl;


XPRBprob Model;
XPRBvar* var_y;
XPRBvar* var_x;
XPRBexpr Math;
XPRBctr * Bounds;
XPRBexpr Objective;

XPRSprob XPRS_Model;
XPRSprob XPRS_Intersection_Model;
void Read_Data(){
    ifstream Input;
    Input.open(Problem);
    Input>> N_Variables;
    Input>> N_Constraints;
    Matrix_obj= new double* [N_Objectives];
    Matrix_contraint = new double* [N_Constraints]; 
    for(int i=0; i<N_Objectives;i++){
        Matrix_obj[i]=new double[N_Variables];
    }
    for(int i=0; i<N_Constraints;i++){
        Matrix_contraint[i] = new double [N_Variables+1];
    }
    
    
    for(int i=0; i<N_Objectives;i++){
        for(int j=0;j<N_Variables;j++){
            Input>>Matrix_obj[i][j];
        }
    }
    
    for(int i=0; i<N_Constraints;i++){
        for(int j=0;j<=N_Variables;j++){
            Input>>Matrix_contraint[i][j];
        }
    }
    
    var_y= new XPRBvar [N_Objectives];
    for(int i=0; i<N_Objectives;i++){
        var_y[i]= Model.newVar("y");
    }
    int type;
    var_x= new XPRBvar [N_Variables];
    for(int i=0; i<N_Variables; i++){
        Input >> type;
        if(type==2){
            var_x[i] = Model.newVar("x",XPRB_PL);
        }else if(type ==3){
            var_x[i] = Model.newVar("x",XPRB_BV);
        }else if(type ==1){
            var_x[i] = Model.newVar("x",XPRB_UI);
        }
    }
    Input.close();
    Variable_value = new double [N_Variables + N_Objectives];
    
    for(int i=0; i<N_Objectives;i++){
        Math.reset();
        Math += var_y[i];
        for(int j=0; j<N_Variables;j++){
            Math -= Matrix_obj[i][j]*var_x[j];
        }
        Model.newCtr( Math == 0.0);
        Math.reset();
    }
    
    for(int i=0; i<N_Constraints;i++){
        Math.reset();
        for(int j=0; j<N_Variables;j++){
            Math += Matrix_contraint[i][j]*var_x[j];
        }
        Model.newCtr( Math <= Matrix_contraint[i][N_Variables]);
        Math.reset();
    }
    
    Y_star = new double [N_Objectives];
    Y = new double [N_Objectives];
    Y_cut = new double [N_Objectives];
    for(int i=0; i<N_Objectives;i++){
        Y_star[i] = 0;
    }
    Variable_value = new double [N_Variables + N_Objectives];
}

bool Check_Cutting_Plane() {
    Check_Value = 0;
    Math.reset();
    for (int i = 0; i < N_Objectives; i++) {
        Math += (W[i]  / Y[i])* var_y[i];
    }
    Model.setObj(Math);
    Math.reset();
    Model.setSense(XPRB_MAXIM);
    XPRSsetintcontrol(XPRS_Model, XPRS_MAXTIME, -T_limit);
    N_LP++;
    Model.mipOptimize();
    status = Model.getMIPStat();
    if (status == XPRB_MIP_OPTIMAL) {
        Check_Value = Model.getObjVal();
        if (Check_Value > Check_RHS) {
            LB = 1;
            XPRSgetmipsol(XPRS_Model, Variable_value, NULL);
            for (int i = 0; i < N_Objectives; i++) {
                Y[i] = Variable_value[i];
                LB *= pow(Y[i], W[i]);
            cout<<i<<" : "<<Y[i]<<" ";
        }
        cout<<endl;
            Math.reset();
            for (int i = N_Objectives; i < N_Variables; i++) {
                if (Variable_value[i] >= 1 - epsilon) {
                    Math += (1 - var_x[i - N_Objectives]);
                } else {
                    Math += var_x[i - N_Objectives];
                }
            }
            Model.newCtr(Math >= 1);
            Math.reset();
            if (LB > epsilon) {
                Math.reset();
                for (int i = 0; i < N_Objectives; i++) {
                    Math += (W[i] / Y[i]) * var_y[i];
                }
                Model.newCtr(Math >= Check_RHS);
                Math.reset();
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
    }else if (status==XPRB_MIP_INFEAS) {
        Search_done=1;
        Global_UB = Global_LB;
    }
    Model.setObj(Objective);
    Model.setSense(XPRB_MAXIM);
}

void WSO() {
    run_start = clock();
    counter++;
    XPRSsetintcontrol(XPRS_Model,XPRS_MAXTIME,-T_limit);
    N_LP++;
    Model.mipOptimize();
    status = Model.getMIPStat();
    if (status == XPRB_MIP_OPTIMAL) {
        Objective_value = Model.getObjVal();
        LB = 1;
        XPRSgetmipsol(XPRS_Model, Variable_value, NULL);
        for(int i=0; i<N_Objectives; i++){
                Y[i]= Variable_value[i];
                LB *= pow(Y[i],W[i]);
            cout<<i<<" : "<<Y[i]<<" ";
        }
        cout<<endl;
        UB = Objective_value / Total_W;
        UB = pow(UB, Total_W);
        if(Global_UB> UB){
            Global_UB = UB;
        }
        Math.reset();
            for (int i = N_Objectives; i < N_Variables; i++) {
                if (Variable_value[i] >= 1 - epsilon) {
                    Math += (1 - var_x[i-N_Objectives]);
                } else {
                    Math += var_x[i-N_Objectives];
                }
            }
            Model.newCtr(Math >= 1);
            Math.reset();
    } else if(status==XPRB_MIP_INFEAS){
        Infeasible = 1;
        Search_done = 1;
        if (counter == 1) {
            cout << "Problem is infeasible" << endl;
        } else {
            Global_UB = Global_LB;
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
        Math.reset();
        for (int i = 0; i < N_Objectives; i++) {
            Math += (W[i] / Y[i]) * var_y[i];
        }
        Model.newCtr(Math >= Check_RHS);
        Math.reset();
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
    while (!Search_done && T_limit > 0 && Global_UB > Global_LB + Abs_Optimal_Tol && (Global_UB - Global_LB) / (Global_UB + denominator) > Rel_Optimal_Tol) {
        WSO();
    }
    
    if (Global_UB <= Global_LB + Abs_Optimal_Tol || (Global_UB - Global_LB) / (Global_UB + denominator) <= Rel_Optimal_Tol) {
        Global_UB = Global_LB;
    }

}

void Writing_Output(){
    ofstream OutputFile;
    OutputFile.open("Results.txt", ios::app);
    OutputFile<<Problem<<" GLB= "<< std::setprecision(Output_Precision) << Global_LB<< " GUB= "<< Global_UB<<" Gap= "<< (Global_UB-Global_LB)/Global_UB << " #VAR= "<< N_Variables  << " #Const= "<< N_Constraints<< " Time= "<< clock_Run_time<<" #IP= "<<N_LP<<" tune= "<<tune_Run_time<<endl;
    OutputFile.close();
}


int main(int argc, char *argv[]) {
    
    Problem = argv[1];
    tuner_lvl = atoi(argv[2]);
    N_Objectives = atoi(argv[3]);
    W= new int [N_Objectives];
    for(int i=0; i< N_Objectives; i++){
        W[i]= atoi(argv[i+4]);
        Total_W += W[i];
    }
    
    Read_Data();
    
    Bounds = new XPRBctr [N_Objectives];

    Objective.reset();
    for(int i=0; i<N_Objectives;i++){
        Objective += W[i]*var_y[i];
    }
    Model.setObj(Objective);
    Model.setSense(XPRB_MAXIM);
    
    XPRS_Model = Model.getXPRSprob();
    Model.setMsgLevel(0);
    
    Model.sync(XPRB_XPRS_PROB);
    gettimeofday(&startTime, NULL);
     
    
    if(tuner_lvl!=0){
    tune_start_time=clock();  
    XPRSsetintcontrol(XPRS_Model, XPRS_TUNEROUTPUT, 0);
    Model.loadMat();
    XPRSsetintcontrol(XPRS_Model,XPRS_THREADS,Num_threads);
    XPRSsetintcontrol(XPRS_Model,XPRS_TUNERMAXTIME,-N_Variables);
    XPRStune(XPRS_Model, "g");   
    tune_Run_time = clock() - tune_start_time;
    tune_Run_time /= CLOCKS_PER_SEC;
    Model.setMsgLevel(3);
    XPRSsetlogfile(XPRS_Model, "tune.prm");
    XPRSdumpcontrols(XPRS_Model);
    Model.setMsgLevel(0);
    }
    
    XPRSsetintcontrol(XPRS_Model,XPRS_THREADS,Num_threads);
    XPRSsetdblcontrol(XPRS_Model,XPRS_MIPABSSTOP,Relative_Gap);
    XPRSsetdblcontrol(XPRS_Model,XPRS_MIPRELSTOP,Relative_Gap);    
    
    Check_RHS=Total_W;
    T_limit = Time_Limit;
    
    clock_start_time = clock();
        
        Algorithm();
        
    gettimeofday(&endTime, NULL);
    clock_Run_time += (clock() - clock_start_time);
    clock_Run_time /= CLOCKS_PER_SEC;
    Writing_Output();
  return 0;
}