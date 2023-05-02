#include "dimacs.h"
#include <ctime>
#include <iostream>
#include <cstring>
#include <cstdio>
#include <algorithm>
#include <cstdlib>

using namespace std;

int dlis(vector<vector<int> > clauses, int clausesCount, char*variableState, char *pendingVarState, int variablesCount, vector<int> variable_freq){
    int max=0;

//One literal clause assignment
    for (int i=0;i<clausesCount;++i){
        if (clauses[i][0]==1){
            if (variableState[abs(clauses[i][1])] == 'x' && pendingVarState[abs(clauses[i][1]) == 'x']){
                
                return (clauses[i][1]);
            }
        }
    }

//Find max literal_freq for variables that are not assigned
    for (int j=1;j<=variablesCount;j++){
        if (abs(variable_freq[j])>max && variableState[j]!='x' && pendingVarState[j]!='x'){
            max=abs(variable_freq[j]);
        }
    }

//Return the literal Among those literals that have the highest unassigned frequency      
    for (int j=1;j<=variablesCount;j++){
        if (abs(variable_freq[j])==max && variableState[j]!='x' && pendingVarState[j]!='x'){
            std::cout<<"The max is "<<max<<"and assignment decision is "<<j*((variable_freq[j])/(abs(variable_freq[j])));
            return j*((variable_freq[j])/(abs(variable_freq[j])));
        }
    }
return 0;
}