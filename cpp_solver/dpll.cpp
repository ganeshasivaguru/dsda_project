#include "dimacs.h"
#include <ctime>
#include <iostream>
#include <cstring>
#include <cstdio>
#include <algorithm>

using namespace std;

void unit_clause_search() {
  // This clause will search the 2D array and search for unit clauses and sets the value of the unit clauses 
  // to variables 
}


void bcp() {





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
       for (int j = 0; j <= clauses[i][0]; ++j) {
         printf("%d ", clauses[i][j]);
       }
       printf("\n");
     }
     // Create an array that is storing the state of the variable
	 // When we create a free decision, or make a implied decision, we set the state of the variable to the corresponding value
	 int *variableState = new int[variablesCount]; //This is the variable assignment state, 
												   //when a decision regarding variable assignment is made this data structure is updated
	 char *clauseState = new char[clausesCount]; //This data structure indicates the status of the clause -> 1:Satisfied 0:Un-Satisfied x:Unresolved
	 int *pendingVarState = new int[variablesCount];//When in the BCP, the decisions are made in the pendingVarState --> when the next free decision is made in the
						  // DPLL main algorithm, the values in the pendingVarState are copied to the variableState data structure.

	 int **watchedLiteral = new int*[clausesCount]; //The watched literal is added as a 2D array, each row corresponds to a clause
	 // Creating the second dimension of the 2D array, and setting intial clauseState to "x"
	 for (int i=0; i < clausesCount; i++) {
	     watchedLiteral[i] = new int[2];		 
		 clauseState[i] = 'x';
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
		     variableState[unit_var] = 1;//Setting the unit clause to 1 when in uncomplemented form
		   } else {
		     variableState[unit_var] = 0; //Setting the unit clause to 0 when in complemented form
		   }
		   clauseState[i] = '1';
         }
	   }
     }
    
     // GVS: Just printing the clauseState to verify it all initial unit clauses are set	 
	 for(int k=0; k<clausesCount; k++) {
	   std::cout << clauseState[k] << " " ;
	 }
	 std::cout << "\n"; 
	 // Boolean Constraint propagation function
	 //

    return 0;
}
