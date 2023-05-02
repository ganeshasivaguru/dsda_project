#!/bin/bash
make build
i=0
#state=();
state=0;
#echo $i
for file in ../../dsda_project_latest/dsda_project/cpp_solver/cnf/*
  do
    if grep -q 'Not satisfiable' "$file"; then
		  state=0;
    else 
		  state=1;
    fi
	#state+=($i)	 
	./mySAT "$file" >> AIM_CNF_logs/result_$i.log
    if grep	-q 'UNSAT' AIM_CNF_logs/result_$i.log; then
	  if [ $state -eq 1 ];then
	    echo "MISSMATCH"
	  fi
    else 
	  if [ $state -eq 0 ]; then
	    echo "MISSMATCH"
      fi
    fi	  


	#echo "$file" >> multiple_runs_log/result_$i.log
    i=$((i+1))
  done
 
echo ${state[@]}	
#if [ "${state[$i]}" -eq 1 ]; then
#   echo "SAT" 
#else 
#   echo "UNSAT"
#fi
#for file in 
#/home/ganesha/dsda_project_latest/cpp_solver/multiple_runs_log/*
#  do
#    if grep	-q 'UNSAT' "$file"; then
#	  if [ ${state[$i]} -eq 1 ];then
#	    echo "MISSMATCH"
#	  fi
#    else 
#	  if [ ${state[$i]} -eq 0 ]; then
#	    echo "MISSMATCH"
#      fi
#    fi	  
#  done
#
#
