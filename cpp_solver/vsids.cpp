#include "dimacs.h"
#include <ctime>
#include <iostream>
#include <cstring>
#include <cstdio>
#include <algorithm>
#include <cstdlib>

using namespace std;

int vsids(int **clauses, int clausesCount, char*variableState, int variablesCount){
    for (int i=0;i<clausesCount;++i){
        if (clauses[i][0]==1){
            if (variableState[abs(clauses[i][1])] == 'x'){
                
                return (clauses[i][1]);
            }
        }
    }
    
    int polarity_select=rand()%2;
    for (int var=0; var<variablesCount; ++var){
        if (variableState[var] = 'x'){
            return var*pow(-1,polarity_select);
        }

    }
}