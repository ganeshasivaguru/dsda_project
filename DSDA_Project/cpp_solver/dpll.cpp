#include "dimacs.h"
#include <ctime>
#include <iostream>
#include <cstring>
#include <cstdio>
#include <algorithm>

using namespace std;

int unit_clause_search() {
  // This clause will search the 2D array and search for unit clauses and sets the value of the unit clauses 
  // to variables 
}


int bcp() {





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
	 //
	 // Boolean Constraint propagation function
	 //

    return 0;
}
