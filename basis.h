#ifndef _BASIS_H_
#define _BASIS_H_

typedef long long LL;

#include "bijection.h"

//#define debug_mode

//#define rand_hard_decreasing_mode
#define ans_op_mode
//#define reset_mode
//#define age_init_0
#define age_init_i

//double second1=1000000.0;

int sp_value;

int time_limit = 295;
int print_speed=50000;
double time_convergence=3.0;
int answer_written = 0;

int flag_weighted = 0;

//cutoff
LL	   max_flips = 20000000000000ll;
LL     flip_bound = 0;

#ifdef last_second_flip_time_mode
LL *last_second_flip_time;
#endif

// Define a data structure for a literal in the SAT problem.
struct lit 
{
    int clause_num;		//clause num, begin with 0
    int var_num;		//variable num, begin with 1
    int sense;			//is 1 for true literals, 0 for false literals.
};

/*parameters of the instance*/
int     var_n;		//var index from 1 to var_n
int     clause_n;	//clause index from 0 to clause_n-1

/* literal arrays */	
/*start from location 0*/			
lit**	var_lit;				//var_lit[i][j] means the j'th literal of var i.
int*	var_lit_count;        //amount of literals of each var
lit**	clause_lit;		//clause_lit[i][j] means the j'th literal of clause i.
int*	clause_lit_count; 	// amount of literals in each clause
//int* 	temp_lit;//				
			
/* Information about the variables. */
LL*     sscore;
LL*		hscore;				
LL*		last_flip_time;
int**	var_neighbor;
int*	var_neighbor_count;

/* Information about the clauses */	
LL sweight_unsat_best;
LL sweight_unsat;
LL weight_hard;
LL*     weight;
int*     sat_n;			
int*	sat_var;

/*for breaking ties randomly*/
int* best_cand_vars;
int	best_cand_var_n;
int best_score_value;

/* Information about runtime performances*/
double time_best =  DBL_MAX;
LL step_best = LLONG_MAX;
int trie_best = INT_MAX;
LL 	   step = 1;
int	   trie = 1;


Bijection 	*ptr_to_hd;
Bijection 	*ptr_to_h0sd;
//variables occurring in unsat hard clauses
int* 		var_n_in_hc0;// to be programmed

Bijection	*ptr_to_vhc0;
Bijection	*ptr_to_sc0;
Bijection	*ptr_to_hc0;
Bijection	*ptr_to_hcw2sat;
//hard clause mark
int*		isHard;

#ifdef ans_op_mode
int ans_n;
int* ans;// from 1 to var_n
int* ans_in;//
#endif

/* Information about solution */
int* value;	//the current solution, with 1's for True variables, and 0's for False variables
int* value_best;//

void free_memory();
int build_instance(char *filename);
void build_neighbor_relation();


void show_best_cand_vars();
#endif
