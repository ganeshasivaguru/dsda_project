#include "dimacs.h"
#include <ctime>
#include <iostream>
#include <cstring>
#include <cstdio>
#include <algorithm>
#include <cstdlib>
#include "vsids.cpp"

using namespace std;


int getPendingVar(int *clause, char *pendingVarState) {
  //std::cout << "getPendingVar " << (pendingVarState[0]) << "\n";
  for(int i=0; i<clause[0]; i++) {
	std::cout << "clause[" << i << "]: " << clause[i+1] << "\n";
	//std::cout << "abs:" << abs(clause[i]) << "\n";
    if(pendingVarState[abs(clause[i+1])-1] == 'x') {
	  std::cout << "returning value:" << clause[i+1] << "\n";
      return clause[i+1];
	}
  }
  return 0;
}

bool checkUnitClauses(char *clauseState, int clausesCount) {
  for(int i=0; i<clausesCount; i++) {
    if(clauseState[i] == 'u') 
	  return true;
  }
  return false;
}


bool bcp(int **clauses, int **watchedLiteral, char *variableState, char *pendingVarState, char *clauseState, int var_assignment, int clausesCount, int variablesCount) {
  std::cout << "Variable assignment is" << var_assignment << "\n";
	 /*for(int k=0; k<clausesCount; k++) {
	   std::cout << clauseState[k] << " " ;
	   std::cout << "Watched literals for clause " << k << "is " << watchedLiteral[k][0] << " & " << watchedLiteral[k][1] << "\n"; 
	   std::cout << "UNSIGNED TRANSFORMATION Watched literals for clause " << k << "is " << (unsigned int) watchedLiteral[k][0] << " & " << (unsigned int) watchedLiteral[k][1] << "\n"; 
	 }*/
  pendingVarState[abs(var_assignment)-1] = (var_assignment > 0) ? '1' : '0'; //variable gets assigned
  for(int i=0; i<clausesCount; ++i) { // cyles through all clauses to 
	//For the variable assignment update the clauseState using updateClauseState function
	//updateClauseState(clauses[i],clauseState,var_assignment,clausesCount,i);
	int updatedWatchedLiteral=0; // This is a flag variable to check if there is new watched literal or not
	if(clauseState[i] == 'x') {
	  std::cout << "Checking for clause " << i << "\n";
	  if(var_assignment == watchedLiteral[i][0] || var_assignment == watchedLiteral[i][1]) {
        //This is the case where the variable assignment matches the watchedLiteral of a clause. This makes the clause satisfied
		clauseState[i] = '1';
	  } else if(abs(var_assignment) == abs(watchedLiteral[i][0]) || abs(var_assignment) == abs(watchedLiteral[i][1])) {
        //This is the case where the variable is in watched literal but in opposite form
		// In this case, if we see that the assignment conflicts a unit clause --> return UNSAT
	    std::cout << "Watched literal was assigned, time to change the watched literal\n" ;
		if(clauseState[i] == 'u') {
          return false; //UNSAT 
	    }
		for(int j=0; j<clauses[i][0]; j++) {
		  if(variableState[abs((clauses[i][j+1]))-1] != 'x' || clauses[i][j+1] == watchedLiteral[i][0] || clauses[i][j+1] == watchedLiteral[i][1]) {
			continue; //Because an assigned variable cannot be set as watched literal
		  } else {
		    std::cout << "Updated watched literal is " << clauses[i][j+1] << "\n";
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
        if(updatedWatchedLiteral !=1) { //Meaning the clause is unit
          clauseState[i] = 'u';
		} 
	  }
	}
  }
  return true;
}


bool bcp_top(int **clauses, int **watchedLiteral, char*variableState, char *pendingVarState, char *clauseState, int var_assignment, int clausesCount, int variablesCount) {
  // The purpose of this is to call the bcp function multiple times for all the unit clauses and return the results to the main function
  // 1. First call bcp with the initial assignment from the main function (i.e. the free decision)
  // 2. On "true" return from the bcp function, go through the clauses and select a unit clause and make it as new assignment and call bcp
  // 3. If the return of BCP is false, then there is UNSAT, send UNSAT to main function.
  // 4. if the return is not false, recall to see the next unit clause and continue the same 
  bool status=bcp(clauses, watchedLiteral, variableState, pendingVarState, clauseState, var_assignment, clausesCount, variablesCount);
  std::cout << "updated status and watched literals\n";
	 for(int k=0; k<clausesCount; k++) {
	   std::cout << clauseState[k] << " " ;
	   std::cout << "Watched literals for clause " << k << "is " << watchedLiteral[k][0] << " & " << watchedLiteral[k][1] << "\n"; 
	 }
  /*std::cout << "\n"; 
	 for(int k=0; k<variablesCount; k++) {
	   std::cout << "Variable " << k << << variableState[k] << " " ;
	 }*/

  if(status != false) {
	while(checkUnitClauses(clauseState,clausesCount)) {
	  std::cout << "There are some unit clauses to take care of \n";
      for(int i=0; i<clausesCount; i++) {
        if(clauseState[i] == 'u') {
		  for(int i=0; i<variablesCount; i++) {
             std::cout << "Pending var state for variable " << i+1 << "is " << pendingVarState[i] << "\n";
		  }
		  std::cout << "Clause no: " << i+1 << " is unit clause\n";
		  std::cout << "clauses[i]" << *clauses[i] << "\n";
		  int sub_var_assgn=getPendingVar(clauses[i],pendingVarState);
		  std::cout << "Sub var assignment is " << sub_var_assgn << "\n";
		  if(sub_var_assgn == 0) {
            // This means even though it is a unit clause, the variable has already been assigned
			// Check if for the unit clause, does it break satisfiability
			for(int j=0; j<clauses[i][0]; i++) {
               if(int(pendingVarState[abs(clauses[i][j])-1]) != clauses[i][j]) {
				//This could be a place to add new conflict clauses
                 return false;
			   }
			}
		  }
		  //pendingVarState[abs(sub_var_assgn)-1] = (sub_var_assgn > 0) ? '1' : '0';
		  //std::cout << "Pending var state of " << abs(sub_var_assgn) << ": " << pendingVarState[abs(sub_var_assgn)-1] << "\n";
		  // Because we are setting the variable assignment based on the unit clause, it means that this clause will become satisfied
		  clauseState[i] = '1';
          bool sub_result = bcp(clauses, watchedLiteral, variableState, pendingVarState, clauseState, sub_var_assgn, clausesCount, variablesCount);
		  if(sub_result == false) {
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

    int **clauses = new int*[clausesCount];

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
      clauses[i] = new int[k+1];
      clauses[i][0] = k;
      //Sort performed to bring all the complemented literals to the front of the array
      sort(buffer, buffer+k);
      memcpy(clauses[i]+1, buffer, size);
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
	 char *clauseState = new char[clausesCount]; //This data structure indicates the status of the clause -> 1:Satisfied 0:Un-Satisfied x:Unresolved
	 char *pendingVarState = new char[variablesCount];//When in the BCP, the decisions are made in the pendingVarState --> when the next free decision is made in the
						  // DPLL main algorithm, the values in the pendingVarState are copied to the variableState data structure.

	 int **watchedLiteral = new int*[clausesCount]; //The watched literal is added as a 2D array, each row corresponds to a clause
	 // Creating the second dimension of the 2D array, and setting intial clauseState to "x"
	 for (int i=0; i < clausesCount; i++) {
		 watchedLiteral[i] = new int[2];		 
		 clauseState[i] = 'x';
     }
	 // Initializing all the variableState to x
	 for (int i=0; i<variablesCount; i++) {
	   variableState[i]='x';
	   pendingVarState[i] = 'x';
	 }
	 //Setting the initial watch literals for all the clauses
	 for(int i=0; i< clausesCount; ++i) {
	   for(int j=0;j<clauses[i][0]; ++j) {
		 if(clauses[i][0] != 1) {
		   watchedLiteral[i][0] = clauses[i][1];
           watchedLiteral[i][1] = clauses[i][2];		   
         } else if (clauses[i][0] == 1) {
           watchedLiteral[i][0] = 0; // 0 indicates that there are no watched literals
		   watchedLiteral[i][1] = 0;
           int unit_var = clauses[i][1];
		   if(unit_var > 0) {
			 variableState[unit_var-1] = '1';//Setting the unit clause to 1 when in uncomplemented form
											 // unit_var - 1 -> because index0 maps to variable 1, index1 maps to variable 2 and soon
		   } else {
			 variableState[unit_var-1] = '0'; //Setting the unit clause to 0 when in complemented form
											 // unit_var - 1 -> because index0 maps to variable 1, index1 maps to variable 2 and soon
		   }
		   clauseState[i] = '1';
         }
	   }
     }
    
     // GVS: Just printing the clauseState to verify it all initial unit clauses are set	 
	 for(int k=0; k<clausesCount; k++) {
	   std::cout << clauseState[k] << " " ;
	   std::cout << "Watched literals for clause " << k << "is " << watchedLiteral[k][0] << " & " << watchedLiteral[k][1] << "\n"; 
	 }

	 std::cout << "\n"; 
	 for(int k=0; k<variablesCount; k++) {
	   std::cout << variableState[k] << " " ;
	 }

	 std::cout << "\n";


	 int assignment_decision; //This variable with be the assigment made, Say var1 is set to 0, then set this to -1, if var2 is set this to 2, soon 
	 // Boolean Constraint propagation function
	 bool result=bcp_top(clauses, watchedLiteral,variableState,pendingVarState, clauseState, 1 , clausesCount,variablesCount);
	 if(result == true) variableState[0] = '1'; 
	 if(result == true) {
       result =bcp_top(clauses, watchedLiteral,variableState,pendingVarState, clauseState, 2 , clausesCount,variablesCount); 
	 }
	 string output_str = (result == 1) ? "SAT" : "UNSAT";
         std::cout << "---------------------------------------------\n";
         std::cout << "Result is " << output_str << "\n";
	     std::cout << "---------------------------------------------\n";
         for(int i=0; i<variablesCount; i++) {
           std::cout << "Variable " << i+1 << "state is " << variableState[i] << "\n";
           std::cout << "Pending Variable " << i+1 << "state is " << pendingVarState[i] << "\n";
         }
         for(int j=0; j<clausesCount; j++) {
           std::cout << "Clause " << j << "state is " << clauseState[j] << "\n";
         }

    return 0;
}
