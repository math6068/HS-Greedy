#include <iostream>
#include <fstream>
#include <cstdlib>
#include <cmath>
#include <sys/times.h> //these two h files are for linux
#include <unistd.h>
#include <string.h>
#include <climits>
#include <cfloat>
#include <ctime>

using namespace std;

//#include "linked_partitions.h"
#include "bijection.h"
#include "basis.h"
#include "memory.h"
#include "debug.h"
#include "dist.h"

int (* pick_var) ();


//set functions in the algorithm
void set_functions()
{	
	flip = flip_3SAT;
	pick_var = pick_var_3SAT;
}

void update_best_solution()
{		
	sweight_unsat_best = sweight_unsat;				
	time_best = double(clock()) / 1000000.0;

	cout << "o " << sweight_unsat_best << endl;
	//cout << "c time " << time_best << endl;

	trie_best = trie;
	step_best = step;
			
#ifdef ans_op_mode			
	for(int i = 1; i <= ans_n; i++)//ans_n is at most as many as the number of steps since last time the best solution is updated
	{
		ans_in[ans[i]] = 0;//necessary, ans_in is used to determine whether a variable is in the updated set			
	}
	ans_n = 0;
#endif
}

//int best_answer=10000000;
void local_search(LL flip_bound)
{  
	while(step <= flip_bound)
	{	
		int v;

		if(!weight_hard || !ptr_to_hc0->size())
			if(sweight_unsat_best > sweight_unsat)
			{
#ifdef debug_mode
//cout << "update best solution" << endl;
#endif
				update_best_solution();
				if(sweight_unsat == 0) return;
			}
/////////////////
		v = pick_var();

		flip(v);
#ifdef debug_mode
//cout << "right after flipping " << v << " in local search func " << endl;
//cout << "sweight_unsat: " << sweight_unsat << endl;
//cout << "hc0.size: " << ptr_to_hc0->size() << endl;
//show_hc0();
//cout << "sc0.size: " << ptr_to_sc0->size() << endl;
//show_sc0();
//print_solution();
//print_score();
if(!check_score()) exit(1);
if(!check_hd() || !check_h0sd()) exit(1);
if(!check_hc0() || !check_sc0()) exit(1);
if(!check_hcw2sat()) exit(1);
if(!check_vhc0()) exit(1);
if(!check_value_valid()) exit(1);
if(!check_cand_solution()) exit(1);
//getchar();
#endif
//////////////////
		if(!(step % 10000))
		{
			if(clock() > time_limit * 1000000.0) return;
		}		
		step++;
	}
}

int main(int argc, char* argv[])
{
	int     seed;
    
	struct tms start, stop;
	times(&start);

	if(build_instance(argv[1]) == 0)
	{
		cout << "Invalid filename: " << argv[1] << endl;
		return -1;
	}
	 
	//sscanf(argv[2], "%d", &seed);
    //srand(seed);
	srand(time(NULL));
    
    //sscanf(argv[3], "%d", &time_limit);    
    
	set_functions();
	
#ifdef reset_mode	
	if(var_n > 100000)
		max_flips = 20000000000000ll;
	else
		max_flips = 20 * var_n;
#else
		max_flips = 20000000000000ll;
#endif
	step = 1;
	trie = 1;
#ifdef debug_mode
cout << "trie: " << trie << endl;
cout << "step: " << step << endl;
#endif

	while(1) 
	{
		 init();	 
#ifdef debug_mode
cout << "initialization succeeds" << endl;
#endif
		 flip_bound += max_flips;
#ifdef debug_mode

#endif	 
		 local_search(flip_bound);

		 if(clock() > time_limit * 1000000.0)
		 {						
			break;
		 }

		 if(ptr_to_hc0->size() == 0 && ptr_to_sc0->size() == 0) break;
		 
		 max_flips <<= 2;

		 trie++;
#ifdef debug_mode
cout << "trie: " << trie << endl;
cout << "step: " << step << endl;
#endif
	}
#ifdef debug_mode
cout << "at the end of the run, step: " << step << endl;
#endif
	times(&stop);
	//double sat_comp_time = double(stop.tms_utime - start.tms_utime +stop.tms_stime - start.tms_stime) / sysconf(_SC_CLK_TCK);

#ifdef ans_op_mode
{
	int v;
	for(v = 1; v <= var_n; v++)
	{
		if(ans_in[v])
			value_best[v] = 1 - value[v];
		else			
			value_best[v] = value[v];
	}
}
#endif	
	if(ptr_to_hc0->size() == 0 && ptr_to_sc0->size() == 0)
	{
		if(verify_sol() == 1)
		{  
			cout << "s OPTIMUM FOUND" << endl;  
//cout << "c solveStep " << step << endl;
//cout << "c solveTime " << sat_comp_time << endl;      
//printf("c flip/ms %.2lf\n", step / ((double)(clock()) / 1000000.0) / 1000.0);
			if(!answer_written)
			{

				//cout << "c verfication successful " << endl;
				//printf("o %lld\n", sweight_unsat_best);
				//cout << "c solveTrie " << trie << endl;			
				Write_answer();
				answer_written = 1;
			}
            //printf("c total_flip_time %lld\n", step);
			//cout << "c totalTrie " << trie << endl;
			//printf("c totalTime %lf\n", double(clock())/1000000.0);

        }
        else 
		{
			cout << "s UNKNOWN" << endl;
			cout << "c Sorry, something is wrong."<<endl;
		}
    }
    else
    {
		//if(!weight_hard || sweight_unsat_best < weight_hard)
		if(Check())
		{
			cout << "s UNKNOWN" << endl;
			//cout << "c verification successful" << endl;
//printf("c searchStep %lld\n", step_best);
//printf("c solveTime %.2lf\n", time_best);
//printf("c flip/ms %.2lf\n", step / ((double)(clock())/1000000.0) / 1000.0);    	  	    	  	
			if(!answer_written)
			{
				//printf("o %lld\n", sweight_unsat_best);
				Write_answer();
				answer_written = 1;
				//cout << "c solveTrie " << trie_best << endl;
			}
				//printf("c total_flip_time %lld\n", step);
				//cout << "c totalTries " << trie << endl;

			
    	

    	//printf("c total_flip_time %lld\n", step);
		//cout << "c totalTrie " << trie << endl;
		//printf("c totalTime %.2lf\n", double(clock()) / 1000000.0);

		//	Write_answer();
    	}
    	else
		{
			puts("s UNKNOWN");
    		puts("c failure.");
		}
	}    		
	
	//printf("c time %.2lf\n", double(clock()) / 1000000.0);
    	  	 
    free_memory();

    return 0;
}
