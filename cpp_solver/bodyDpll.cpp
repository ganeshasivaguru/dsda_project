#include "dimacs.h"
#include <ctime>
#include <iostream>
#include <cstring>
#include <cstdio>
#include <algorithm>
#include <cstdlib>
#include <vector>
#include <bits/stdc++.h>

bool SATCheck(vector<vector<int>> &clauses, vector<vector<int> &watchedLiteral, char *variableState, char *pendingVarState, vector<char> clauseState, int clausesCount, int variablesCount, vector<int> &variable_freq, int var_assign) {

  // Pick the variable to assign
  //int test_variable = variable_freq.begin();
  // Currently picking the first variable
  //int var_assign = 1;

  char * copypendingVarState;
  vector<char> copyClauseState;

  memcpy(copypendingVarState, pendingVarState, variablesCount); //Creating the copy as when the complemented form is tested you need a fresh set of assignments
  
  copyclauseState = clauseState;
  bool statewith1; // This will be assigned if result with assignment 1 results in a SAT
  
  bool BCPwith1 = bcp_top(clauses, watchedLiteral, variableState, pendingVarState, clauseState, var_assign, clausesCount, variablesCount);

  if (BCPwith1 == true && !checkClauseState(clauseState, clausesCount)) {
     // SAT with the current pending var assignment
	 // SET solution variable with the values in pending var
	 statewith1=true; 
  } else if (BCPwith1 == true && checkClauseState(clauseState,clausesCount)) {
     // pick next variable and call SATCheck
	 bool nextTrywith1 = SATCheck(clauses,watchedLiteral,variableState,pendingVarState, clauseState, var_assign+1,clausesCount, variablesCount);
     statewith1=(nextTrywith1 == true) ? true : false;
  } else {
    statewith1 = false;
  }
  
  if(statewith1 == true) {
	return true;
  }

  int var_assign *= -1 ;

  bool statewith0;
  bool BCPwithN1 = bcp_top(clauses, watchedLiteral, variableState, copypendingVarState, copyclausesState, var_assign, clausesCount, variablesCount);

  if(BCPwithN1 == true && !checkClauseState(copyclauseState,clausesCount)) {
	 // All clauses are SAT, so terminate
     // SAT with the current pending var assignment
	 clauseState = copyclauseState;
	 memcpy(pendingVarState,copypendingVarState,variablesCount);
	 statewith0 = true;
  } else if (BCPwithN1 == true && checkClauseState(copyclauseState,clausesCount)) {
     // pick next variable and call SATCheck
	 bool nextTrywith0 = SATCheck(clauses, watchedLiteral, variableState, copypendingVarState, copyclauseState,var_assign-1,variablesCount);
	 statewith0 = (nextTrywith0 == true) ? true : false;
  } else {
     statewith0 = false;
  }
    
  return (statewith0 | statewith1);
}
