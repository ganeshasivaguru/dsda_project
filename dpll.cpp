#include "dimacs.h"
#include <ctime>
#include <iostream>
#include <cstring>
#include <cstdio>
#include <algorithm>
#include <cstdlib>
#include <vector>
#include <bits/stdc++.h>

using namespace std;


int getPendingVar(vector<int> clause, char *pendingVarState) {
  //std::cout << "getPendingVar " << (pendingVarState[0]) << "\n";
  for(int i=0; i<clause[0]; i++) {
	//std::cout << "clause[" << i << "]: " << clause[i+1] << "\n";
	//std::cout << "abs:" << abs(clause[i]) << "\n";
    if(pendingVarState[abs(clause[i+1])-1] == 'x') {
	  //std::cout << "returning value:" << clause[i+1] << "\n";
      return clause[i+1];
	}
  }
  return 0;
}

bool checkUnitClauses(vector<char> &clauseState, int clausesCount) {
  for(int i=0; i<clausesCount; i++) {
    if(clauseState[i] == 'u') 
	  return true;
  }
  return false;
}

int nextUnassignedPendingVar(char *variableState, char *pendingVarState, int variableCount) {
  for(int i=0; i<variableCount; i++) {
    if(variableState[i] == 'x' && pendingVarState[i] == 'x') {
      return i+1;
	}
  }
  return 0;
}	

bool checkClauseState(vector<char> &clauseState, int clausesCount) {
  for(int i=0; i<clausesCount; i++) {
    if(clauseState[i] != '1')  
	  return true;//any 1 non-sat clause
  }
  return false;//all clause sat
}	

/*int addConflictClause(int i, int **clauses, int **watchedLiteral, char *variableState, char *pendingVarState, char *clauseState, int var_assignment, int clausesCount, int variablesCount) {

  return 0;
}*/

bool bcp(vector<vector<int>> &clauses, vector<vector<int>> &watchedLiteral, char *variableState, char *pendingVarState, vector<char> &clauseState, int var_assignment, int clausesCount, int variablesCount) {
  //std::cout << "Variable assignment is" << var_assignment << "\n";
	 /*for(int k=0; k<clausesCount; k++) {
	   std::cout << clauseState[k] << " " ;
	   std::cout << "Watched literals for clause " << k << "is " << watchedLiteral[k][0] << " & " << watchedLiteral[k][1] << "\n"; 
	   std::cout << "UNSIGNED TRANSFORMATION Watched literals for clause " << k << "is " << (unsigned int) watchedLiteral[k][0] << " & " << (unsigned int) watchedLiteral[k][1] << "\n"; 
	 }*/
		  /*for(int i=0; i<variablesCount; i++) {
             std::cout << "Pending var state for variable " << i+1 << "is " << pendingVarState[i] << "\n";
		  }*/
  pendingVarState[abs(var_assignment)-1] = (var_assignment > 0) ? '1' : '0'; //variable gets assigned
  for(int i=0; i<clausesCount; ++i) { // cyles through all clauses to 
	int flag_to_set_clause_1 = 0;	  
	//For the variable assignment update the clauseState using updateClauseState function
	//updateClauseState(clauses[i],clauseState,var_assignment,clausesCount,i);
	int updatedWatchedLiteral=0; // This is a flag variable to check if there is new watched literal or not
	if(clauseState[i] == 'x' || clauseState[i] == 'u') {

	  if(clauses[i][0] == 1) {
         if(var_assignment == clauses[i][1]) {
				 clauseState[i] = '1';
		 } else if (abs(var_assignment) == abs(clauses[i][1])) { 
				clauseState[i] = '0';
		        return false; //UNSAT 
		 }
	  }
	  //std::cout << "Checking for clause " << i << "\n";
	  if(var_assignment == watchedLiteral[i][0] || var_assignment == watchedLiteral[i][1]) {
        //This is the case where the variable assignment matches the watchedLiteral of a clause. This makes the clause satisfied
		clauseState[i] = '1';
	  } else if(abs(var_assignment) == abs(watchedLiteral[i][0]) || abs(var_assignment) == abs(watchedLiteral[i][1])) {
        //This is the case where the variable is in watched literal but in opposite form
		// In this case, if we see that the assignment conflicts a unit clause --> return UNSAT
	    //std::cout << "Watched literal was assigned, time to change the watched literal\n" ;
		if(clauseState[i] == 'u') {
		  clauseState[i] = '0'; //Setting that the clause doesnt get SAT
          return false; //UNSAT 
	    }
		for(int j=0; j<clauses[i][0]; j++) {
		  if((variableState[abs((clauses[i][j+1]))-1] != 'x' || pendingVarState[abs((clauses[i][j+1]))-1] != 'x') || clauses[i][j+1] == watchedLiteral[i][0] || clauses[i][j+1] == watchedLiteral[i][1]) {
			// If the non-watched literal variable is assigned a value that satisfies the clause --> set a flag and use that to set the clause state to 1
			if((pendingVarState[abs((clauses[i][j+1]))-1] == '1' && clauses[i][j+1] > 0) || (pendingVarState[abs((clauses[i][j+1]))-1] == '0' && clauses[i][j+1] < 0))
				flag_to_set_clause_1 = 1;
			continue; //Because an assigned variable cannot be set as watched literal
		  } else {
		    //std::cout << "Updated watched literal is " << clauses[i][j+1] << "\n";
			//std::cout << "variable state of updated watched literal is : " << variableState[abs((clauses[i][j+1]))-1] << endl;
            //std::cout << "Pending variable state of the updated watched literal is : " << variableState[abs((clauses[i][j+1]))-1] << endl;
            if(abs(var_assignment) == abs(watchedLiteral[i][0])) {
              watchedLiteral[i][0] = clauses[i][j+1];
			  updatedWatchedLiteral++;
			  break;
			} else if (abs(var_assignment) == abs(watchedLiteral[i][1])) {
              watchedLiteral[i][1] = clauses[i][j+1];
			  updatedWatchedLiteral++;
			  break;
			}
		  }
		// If updatedWatchedLiteral is not changed --> Implies there is no new watch literal --> this is now a unit clause
        }
        if(updatedWatchedLiteral !=1 && !flag_to_set_clause_1) { //Meaning the clause is unit
          clauseState[i] = 'u';
		} else if (updatedWatchedLiteral != 1 && flag_to_set_clause_1) {
          clauseState[i] = '1';
		}
	  }
	}
  }
  return true;
}

bool bcp_top(vector<vector<int>> &clauses, vector<vector<int>> &watchedLiteral, char*variableState, char *pendingVarState, vector<char> &clauseState, int var_assignment, int clausesCount, int variablesCount) {
  // The purpose of this is to call the bcp function multiple times for all the unit clauses and return the results to the main function
  // 1. First call bcp with the initial assignment from the main function (i.e. the free decision)
  // 2. On "true" return from the bcp function, go through the clauses and select a unit clause and make it as new assignment and call bcp
  // 3. If the return of BCP is false, then there is UNSAT, send UNSAT to main function.
  // 4. if the return is not false, recall to see the next unit clause and continue the same 
  bool status=bcp(clauses, watchedLiteral, variableState, pendingVarState, clauseState, var_assignment, clausesCount, variablesCount);
  /*std::cout << "updated status and watched literals\n";
	 for(int k=0; k<clausesCount; k++) {
	   std::cout << clauseState[k] << " " ;
	   std::cout << "Watched literals for clause " << k << "is " << watchedLiteral[k][0] << " & " << watchedLiteral[k][1] << "\n"; 
	 }*/
  /*std::cout << "\n"; 
	 for(int k=0; k<variablesCount; k++) {
	   std::cout << "Variable " << k << << variableState[k] << " " ;
	 }*/

  if(status != false) {
	while(checkUnitClauses(clauseState,clausesCount)) {
	  //std::cout << "There are some unit clauses to take care of \n";
      for(int i=0; i<clausesCount; i++) {
        if(clauseState[i] == 'u') {
		  //for(int i=0; i<variablesCount; i++) {
          //   std::cout << "Pending var state for variable " << i+1 << "is " << pendingVarState[i] << "\n";
		  //}
		  //std::cout << "Clause no: " << i+1 << " is unit clause\n";
		  //std::cout << "clauses[i]" << *clauses[i] << "\n";
		  int sub_var_assgn=getPendingVar(clauses[i],pendingVarState);
		  //std::cout << "Sub var assignment is " << sub_var_assgn << "\n";
		  /*if(sub_var_assgn == 0) {
            // This means even though it is a unit clause, the variable has already been assigned
			// Check if for the unit clause, does it break satisfiability
			for(int j=0; j<clauses[i][0]; i++) {
               if(int(pendingVarState[abs(clauses[i][j])-1]) != clauses[i][j]) {
				//This could be a place to add new conflict clauses
                 return false;
			   }
			}
		  }*/
		  //pendingVarState[abs(sub_var_assgn)-1] = (sub_var_assgn > 0) ? '1' : '0';
		  //std::cout << "Pending var state of " << abs(sub_var_assgn) << ": " << pendingVarState[abs(sub_var_assgn)-1] << "\n";
		  // Because we are setting the variable assignment based on the unit clause, it means that this clause will become satisfied
		  clauseState[i] = '1';
          bool sub_result = bcp(clauses, watchedLiteral, variableState, pendingVarState, clauseState, sub_var_assgn, clausesCount, variablesCount);
	      //for(int k=0; k<clausesCount; k++) {
	      //   std::cout << clauseState[k] << " " ;
          //}
		  if(sub_result == false) {
			// adding conflict clauses
			//addConflictClause(i,clauses,watchedLiteral,variableState,pendingVarState,clauseState,sub_var_assgn,clausesCount,variablesCount);

            return false; //i.e for the initial assignment with the current pendingVar, there is UNSAT
		  }
	    } 
	  }
    }
  } else if (status == false) {
    return false; // UNSAT	
  }
  return true; //i.e for the initial assignment an with all the assignments in pendingVar, there is either SAT or requirement for a new free assignment
}

bool SATCheck(vector<vector<int>> &clauses, vector<vector<int>> &watchedLiteral, char *variableState, char *pendingVarState, vector<char> &clauseState, int clausesCount, int variablesCount, vector<int> &variable_freq, int var_assign) {

  // Pick the variable to assign
  //int test_variable = variable_freq.begin();
  // Currently picking the first variable
  //int var_assign = 1;
  //
		//std::cout << "entering SAT check" << endl;

  char * copypendingVarState = new char[variablesCount];
  vector<char> copyclauseState;

  memcpy(copypendingVarState, pendingVarState, variablesCount); //Creating the copy as when the complemented form is tested you need a fresh set of assignments
  //std::cout <<"Memcpy successful" << endl; 

  copyclauseState = clauseState;
  bool statewith1, nextTrywith1; // This will be assigned if result with assignment 1 results in a SAT
  
  bool BCPwith1 = bcp_top(clauses, watchedLiteral, variableState, pendingVarState, clauseState, var_assign, clausesCount, variablesCount);

  if (BCPwith1 == true && !checkClauseState(clauseState, clausesCount)) {
     // SAT with the current pending var assignment
	 // SET solution variable with the values in pending var
	 statewith1=true; 
  } else if (BCPwith1 == true && checkClauseState(clauseState,clausesCount)) {
     // pick next variable and call SATCheck
	 // select the next unassigned variable
	 int potential_next_var = nextUnassignedPendingVar(variableState,pendingVarState, variablesCount);
	 if(potential_next_var != 0) {
	 	nextTrywith1 = SATCheck(clauses,watchedLiteral,variableState,pendingVarState, clauseState,clausesCount,variablesCount,variable_freq, potential_next_var);
     } else {
        std::cout << "There is some error in the code" << endl;
		nextTrywith1 = false;
	 }
     statewith1=(nextTrywith1 == true) ? true : false;
  } else {
    statewith1 = false;
  }
  
  if(statewith1 == true) {
	return true;
  } else if (statewith1 == false) {
    //std::cout << "Variable assignement that is not working is : " << var_assign << endl;
	//std::cout << "Backtracking and checking the other path" << endl;
  } 

  var_assign *= -1 ;

  bool statewith0,nextTrywith0; 
  bool BCPwithN1 = bcp_top(clauses, watchedLiteral, variableState, copypendingVarState, copyclauseState, var_assign, clausesCount, variablesCount);

  if(BCPwithN1 == true && !checkClauseState(copyclauseState,clausesCount)) {
	 // All clauses are SAT, so terminate
     // SAT with the current pending var assignment
	 clauseState = copyclauseState;
	 memcpy(pendingVarState,copypendingVarState,variablesCount);
	 statewith0 = true;
  } else if (BCPwithN1 == true && checkClauseState(copyclauseState,clausesCount)) {
     // pick next variable and call SATCheck
	 // select the next unassigned variable
	 int potential_next_var = nextUnassignedPendingVar(variableState,copypendingVarState, variablesCount);
	 if(potential_next_var != 0) {
	 	nextTrywith0 = SATCheck(clauses, watchedLiteral, variableState, copypendingVarState, copyclauseState, clausesCount, variablesCount, variable_freq, potential_next_var);
	 	clauseState = copyclauseState;
	 	memcpy(pendingVarState,copypendingVarState,variablesCount);
     } else {
        std::cout << "There is some error in the code" << endl;
		nextTrywith0 = false;
	 }
	 statewith0 = (nextTrywith0 == true) ? true : false;
  } else {
     statewith0 = false;
  }
    
  //std::cout << "Unsat here: " << (statewith1 | statewith0) << endl;
  //std::cout << "Var assign is " << var_assign << endl;
  return (statewith0 | statewith1);
}




int main(int argc, char **argv) 
{
    if (argc != 2) {
      cout << "Syntax: basic_solver <filename.cnf>" << endl;
      return -1;
    }
    if (freopen(argv[1], "r", stdin) == 0) {
      cout << "Syntax: basic_solver <filename.cnf>" << endl;
      cout << "Cannot open " << argv[1] << endl;
      return -1;
    }
      
    int variablesCount = 0;
    int clausesCount = 0;

    //clock_t t_start_parse = clock();
    cout << "c Parsing SAT problem" << endl;
    if (!parse_problem_header(cin, variablesCount, clausesCount)) {
      cout << "Error reading problem header\n" << endl;
      return -1;
    }

	vector<vector<int>> clauses;

    for (int i = 0; i < clausesCount; ++i) {
      int k;
      int size;
      int *buffer;
      buffer = read_next_clause(cin, variablesCount, k, size);
      // k is the number of literals in a particular clause. This is appended to the start of the 2D array
      if (!buffer) {
        cout << "Error reading clause " << i << endl;
        return -1;
      }
	  vector<int> buf;
	  for(int i=0;i<k; i++) {
		buf.push_back(buffer[i]);
	  }
	  buf.insert(buf.begin(),k);
	  clauses.push_back(buf);
    }
    //printf("c Time to read: %.2fs\n", (double)(clock() - t_start_parse)/CLOCKS_PER_SEC);

     for (int i = 0; i < clausesCount; ++i) {
	   std::cout << "Clause No: " << i;
       for (int j = 0; j <= clauses[i][0]; ++j) {
         printf(" %d ", clauses[i][j]);
       }
       printf("\n");
     }
	 
     // Create an array that is storing the state of the variable
	 // When we create a free decision, or make a implied decision, we set the state of the variable to the corresponding value
	 char *variableState = new char[variablesCount]; //This is the variable assignment state, 
												   //when a decision regarding variable assignment is made this data structure is updated
												   //0 - indicates variable set to 0, 1 - indicates variable set to 1, x - indicates variable is unset 
	 //char *clauseState = new char[clausesCount]; //This data structure indicates the status of the clause -> 1:Satisfied 0:Un-Satisfied x:Unresolved
	 char *pendingVarState = new char[variablesCount];//When in the BCP, the decisions are made in the pendingVarState --> when the next free decision is made in the
						  // DPLL main algorithm, the values in the pendingVarState are copied to the variableState data structure.

     // Adding vectors for clauseState and watchedLiterals as they can potentially increase when conflict driven learning is used.
	 vector<char> clauseState (clausesCount,'x');
	 vector<vector<int>> watchedLiteral;

	 //int **watchedLiteral = new int*[clausesCount]; //The watched literal is added as a 2D array, each row corresponds to a clause
	 // Creating the second dimension of the 2D array, and setting intial clauseState to "x"
	 /*for (int i=0; i < clausesCount; i++) {
		 //watchedLiteral[i] = new int[2];
          
		 clauseState[i] = 'x';
     }*/

	 // Initializing all the variableState to x
	 for (int i=0; i<variablesCount; i++) {
	   variableState[i]='x';
	   pendingVarState[i] = 'x';
	 }
	 
	 //Setting the initial watch literals for all the clauses
	 for(int i=0; i< clausesCount; ++i) {
		vector<int> watchedLiteral_temp;
	   //for(int j=0;j<clauses[i][0]; ++j) {
		 if(clauses[i][0] != 1) {
			//std::cout << "size of clause " << clauses[i][0] << endl;
			watchedLiteral_temp.push_back(clauses[i][1]);
			//std::cout << "clause [i][2] " << clauses[i][2] << endl;
 			watchedLiteral_temp.push_back(clauses[i][2]);
			watchedLiteral.push_back(watchedLiteral_temp);
         } else if (clauses[i][0] == 1) {
			watchedLiteral_temp.push_back(0);
			watchedLiteral_temp.push_back(0);
			watchedLiteral.push_back(watchedLiteral_temp);
           int unit_var = clauses[i][1];
		   if(unit_var > 0) {
			 variableState[unit_var-1] = '1';//Setting the unit clause to 1 when in uncomplemented form
											 // unit_var - 1 -> because index0 maps to variable 1, index1 maps to variable 2 and soon
		   } else {
			 variableState[unit_var-1] = '0'; //Setting the unit clause to 0 when in complemented form
											 // unit_var - 1 -> because index0 maps to variable 1, index1 maps to variable 2 and soon
		   }
		   clauseState[i] = 'u';
         }
	   //}
     }
    
     // GVS: Just printing the clauseState to verify it all initial unit clauses are set	 
	 //for(int k=0; k<clausesCount; k++) {
	 //  std::cout << clauseState[k] << " " ;
	 //  std::cout << "Watched literals for clause " << k << "is " << watchedLiteral[k][0] << " & " << watchedLiteral[k][1] << "\n"; 
	 //}

	 std::cout << "\n"; 
	 //for(int k=0; k<variablesCount; k++) {
	 //  std::cout << variableState[k] << " " ;
	 //}

	 std::cout << "\n";

	 // Vector to indicate the frequency of each variable -- will use in branch decision
	 vector<int> variable_freq (variablesCount,0);

	 //for(int i =0; i< variablesCount; ++i) {
       for(int j=0; j<clausesCount; ++j) {
		  for(int k=0; k<clauses[j][0]; ++k) {
		    //std::cout << abs(clauses[j][k+1]);
			variable_freq[abs(clauses[j][k+1])-1]++;
		  }
	   }
	 //}

	  //for(int i=0; i<variablesCount; i++) {
	  //  std::cout << "Variable  " << i+1 << ": " << variable_freq[i] << endl;
	  //}
      size_t max_val = *max_element(variable_freq.begin(),variable_freq.end());
	  auto index=find(variable_freq.begin(),variable_freq.end(),max_val);
	  int max_index = index - variable_freq.begin();
	  //std::cout << "-------------------------------------" << endl;
	  //std::cout << max_index+1 << endl;
	  //std::cout << "-------------------------------------" << endl;
	  // Steps to run DPLL.
	  // Pick the variable with the max frequency and assign it a value
	  // then call BCP. If BCP return false. reset all the pendingVar state, reset all the clause state and then call the BCP with negative value of max frequency.
	  // if that also returns false ==> the problem is UNSAT.
	  // If the BCP returns true in any one case, check if all the caluses are satisfied --> If yes then the problem is SAT and the values in the pendingVar is the assignment values
	  // if BCP returns true but not all clauses are satisfied --> check for the next highest variable that can be assigned and assign it to a value and call this recursively until you reach a SAT 



	 int assignment_decision = 1; //This variable with be the assigment made, Say var1 is set to 0, then set this to -1, if var2 is set this to 2, soon 
	 bool result = SATCheck(clauses, watchedLiteral, variableState, pendingVarState, clauseState, clausesCount, variablesCount, variable_freq, assignment_decision);
	 // Boolean Constraint propagation function
	 //bool result=bcp_top(clauses, watchedLiteral,variableState,pendingVarState, clauseState, 1 , clausesCount,variablesCount);
	 //if(result == true) variableState[0] = '1'; 
	 //if(result == true) {
     //  result =bcp_top(clauses, watchedLiteral,variableState,pendingVarState, clauseState, 2 , clausesCount,variablesCount); 
	 //}
	 // Solution is the union of the variable states in VariableState and pendingVarstate arrays
	 if (result == 1) {
       // Assign pendingVar state to variable State 
	   for(int i=0; i<variablesCount; i++) {
         variableState[i] = pendingVarState[i];
	   }
	   int no_of_satisfied_clauses=0;
	   // then call the result check function to validate the solution
	   for(int j=0; j<clausesCount; j++) {
	     for(int k=0; k<clauses[j][0]; k++) {
           int clause_element = clauses[j][k+1];
		   int clause_state = (variableState[abs(clause_element)-1] == '1') ? 1 : (variableState[abs(clause_element)-1] == '0') ? 0 : -1 ;
		   if((clause_element > 0 && clause_state == 1) || (clause_element < 0 && clause_state == 0)) {
             no_of_satisfied_clauses++;
			 break;
		   }
	     }
	   }
	   if(no_of_satisfied_clauses == clausesCount) std::cout << "The variables assignment satisfies all the clauses" << endl;
	   else std::cout << "##@@##@@ ##$!@@# Some error with the Solver :( :(  No_of_Satisfied_clauses: " << no_of_satisfied_clauses << "no of clause" << clausesCount << endl; 
	 }
	 string output_str = (result == 1) ? "SAT" : "UNSAT";
         std::cout << "---------------------------------------------\n";
         std::cout << "Result is " << output_str << "\n";
	     std::cout << "---------------------------------------------\n";
		 std::cout << "ASSIGNMENT: " ;
		 for(int i=0; i<variablesCount; i++) {
           //std::cout << "Variable " << i+1 << "state is " << variableState[i];
		   std::cout << "V" << i+1 << "= " << variableState[i] << " " ;
           //std::cout << "Pending Variable " << i+1 << "state is " << pendingVarState[i] << "\n";
         }
		 std::cout << endl;
         //for(int j=0; j<clausesCount; j++) {
         //  std::cout << "Clause " << j << "state is " << clauseState[j] << "\n";
         //}
	
    return 0;
}
