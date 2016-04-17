#ifndef _DIST_H
#define _DIST_H

#include <iostream>
#include <cstdlib>
using namespace std;

#include "basis.h"

//initiation of the algorithm

int init_try = 1;

#ifdef ans_op_mode
void Ans_update(int flipvar)
{
	int v, i;
	if(!ans_in[flipvar])
	{
		ans[++ans_n] = flipvar;
		ans_in[flipvar] = ans_n;
	}
	else
	{
		v = ans[ans_n--];	
		i = ans_in[flipvar];
		ans[i] = v;
		ans_in[v] = i;	
		ans_in[flipvar] = 0;
	}
}
#endif

void init()
{
	int 		v, c;
	int			i, j;
	int			clause;

	ptr_to_hc0->clear();
	ptr_to_sc0->clear();
	ptr_to_hcw2sat->clear();
	ptr_to_hd->clear();
	ptr_to_h0sd->clear();
	ptr_to_vhc0->clear();

	if(init_try)
	{	
#ifdef ans_op_mode
		ans_n = 0;
		for(v = 1; v <= var_n; v++)
		{
			ans[v] = 0;
			ans_in[v] = 0;
		}		
#endif		
		for(v = 1; v <= var_n; v++)
			value[v] = 0;
	}
	//init solution
	for(v = 1; v <= var_n; v++) 
	{
		if(rand() % 2) 
		{
			value[v] = 1 - value[v];		
#ifdef ans_op_mode
			if(!init_try)
			{
				Ans_update(v);
			}
#endif
		}
	}
	for(v = 1; v <= var_n; v++)
	{
		if(init_try)
			value_best[v] = value[v];
		
#ifdef age_init_0
		last_flip_time[v] = 0;
	#ifdef last_second_flip_time_mode
		last_second_flip_time[v] = 0;
	#endif
#endif		

#ifdef age_init_i
		last_flip_time[v] = v - 1 - var_n;
	#ifdef last_second_flip_time_mode
		last_second_flip_time[v] = v - 1 - var_n;
	#endif
#endif
	}

	for(v = 1; v <= var_n; ++v)
	{
		var_n_in_hc0[v] = 0;
	}
	/* figure out sat_n, and init sc0 */
	for(c = 0; c < clause_n; ++c) 
	{
		sat_n[c] = 0;
		
		for(j = 0; j < clause_lit_count[c]; ++j)
		{
			if(value[clause_lit[c][j].var_num] == clause_lit[c][j].sense)
			{
				v = clause_lit[c][j].var_num;
				sat_n[c]++;	
				if(sat_n[c] == 1)		
					sat_var[c] = v;				
			}
		}

		if(sat_n[c] == 0) 
		{
#ifdef debug_mode
cout << "clause " << c << " is unsat." << endl;
#endif
			if(isHard[c])
			{
#ifdef debug_mode
cout << "unsat hard clause " << c << " enters hc0" << endl;
#endif
				ptr_to_hc0->insert_element(c);
				for(lit* p = clause_lit[c]; (v = p->var_num) != 0; p++)
				{
					if(!ptr_to_vhc0->element_in(v))
					{
						ptr_to_vhc0->insert_element(v);
					}
					var_n_in_hc0[v]++;
				}	
			}
			else
			{
#ifdef debug_mode
cout << "unsat soft clause " << c << " enters sc0" << endl;
#endif
				ptr_to_sc0->insert_element(c);
			}
		}
	}
#ifdef debug_mode
cout << "right after initializing hc0 and sc0" << endl;
show_hc0();
show_sc0();
#endif		
	sweight_unsat = 0;
	for(c = 0; c < clause_n; c++)
	{
		if(sat_n[c] == 0 && !isHard[c])
		{
			sweight_unsat += weight[c];
		}
	}
	
	if(init_try)
	{
		if(weight_hard == 0)
		{
			sweight_unsat_best = sweight_unsat;
		}
		else
		{
			sweight_unsat_best = LLONG_MAX;
		}
	}

	/*figure out var hscore and sscore*/
	int lit_count;
	for(v = 1; v <= var_n; v++) 
	{
		sscore[v] = 0;
		hscore[v] = 0;
		lit_count = var_lit_count[v];
		
		for(i = 0; i < lit_count; ++i)
		{
			c = var_lit[v][i].clause_num;
			if(isHard[c])
			{
				if(sat_n[c] == 0)
				{
					hscore[v] += weight[c];
				}
				else if(sat_n[c] == 1 && var_lit[v][i].sense == value[v]) {hscore[v] -= weight[c];}
			}
			else
			{
				if(sat_n[c] == 0) sscore[v] += weight[c];
				else if(sat_n[c] == 1 && var_lit[v][i].sense == value[v]) sscore[v] -= weight[c];			
			}
		}
	}
#ifdef debug_mode
print_solution();
print_score();
cout << "about to add to hd and h0sd" << endl;
#endif
	for(v = 1; v <= var_n; v++)
	{
#ifdef debug_mode
//cout << "considering " << v << ", hard score is " << hscore[v] << ", soft score is " << sscore[v] << endl;
#endif
		if(hscore[v] > 0)
		{
			ptr_to_hd->insert_element(v);
		}
		else if(hscore[v] == 0 && sscore[v] > 0)
		{
			ptr_to_h0sd->insert_element(v);
		}
#ifdef debug_mode
show_hd();
show_h0sd();
//getchar();
#endif
	}

	//setting for the virtual var 0
	last_flip_time[0] = 0;
	init_try = 0;	
#ifdef debug_mode
//cout << "at the end of init()" << endl;
show_vhc0();
if(!check_score()) exit(1);
//cout << "0" << endl;
show_hd();
if(!ptr_to_hd->check()) exit(1); 
//cout << "0.5" << endl;
if(!ptr_to_h0sd->check()) exit(1); 
//cout << "0.75" << endl;
if(!check_hd() || !check_h0sd()) exit(1);
//cout << "1" << endl;
if(!ptr_to_hc0->check() || !ptr_to_sc0->check() || !check_hc0() || !check_sc0()) exit(1);
//cout << "2" << endl;
if(!ptr_to_hcw2sat->check() || !check_hcw2sat()) exit(1);
//cout << "3" << endl;
if(!ptr_to_vhc0->check() || !check_vhc0()) exit(1);
//cout << "4" << endl;
if(!check_value_valid()) exit(1);
if(!check_cand_solution()) exit(1);
cout << "sweight_unsat: " << sweight_unsat << endl;
cout << "hc0.size: " << ptr_to_hc0->size() << endl;
show_hc0();
cout << "sc0.size: " << ptr_to_sc0->size() << endl;
show_sc0();
#endif
}
inline void update_hd_and_h0sd(int v)
{
	if(hscore[v] > 0)
	{
		if(!ptr_to_hd->element_in(v))
		{
			ptr_to_hd->insert_element(v);
		}
		if(ptr_to_h0sd->element_in(v))
		{
			ptr_to_h0sd->delete_element(v);
		}
	}
	else if(hscore[v] == 0 && sscore[v] > 0)
	{
		if(!ptr_to_h0sd->element_in(v))
		{
			ptr_to_h0sd->insert_element(v);
		}
		if(ptr_to_hd->element_in(v))
		{
			ptr_to_hd->delete_element(v);
		}		
	}
	else
	{
		if(ptr_to_hd->element_in(v))
		{
			ptr_to_hd->delete_element(v);
		}	
		if(ptr_to_h0sd->element_in(v))
		{
			ptr_to_h0sd->delete_element(v);
		}
	}	
}

///f3
void flip_3SAT(int flipvar)
{
#ifdef debug_mode
//cout << "having just entering flip_3SAT, with flipvar " << flipvar << endl;
//print_score();
#endif
	value[flipvar] = 1 - value[flipvar];
	
	int i, j;
	int v, c;
	lit* clause_c;

#ifdef ans_op_mode
	Ans_update(flipvar);
#endif
	
	int org_flipvar_sscore = sscore[flipvar];
	int org_flipvar_hscore = hscore[flipvar];

	//update related clauses and neighbor vars
	for(lit *q = var_lit[flipvar]; (c = q->clause_num) >= 0; q++)
	{
#ifdef debug_mode
//cout << "considering clause " << c << endl;
#endif
		clause_c = clause_lit[c];
		if(value[flipvar] == q->sense)
		{
			++sat_n[c];			
			if(sat_n[c] == 2) //sat_n from 1 to 2
			{
				if(isHard[c])
				{
					hscore[sat_var[c]] += weight[c];
				}
				else
				{	
					sscore[sat_var[c]] += weight[c];	
				}				
			}
			else if(sat_n[c] == 1) // sat_n from 0 to 1
			{
				sat_var[c] = flipvar;//record the only true lit's var
				if(isHard[c])
				{
					for(lit* p = clause_c; (v = p->var_num) != 0; p++) 
					{
						if(v != flipvar)
						{
							hscore[v] -= weight[c];	
						}
						var_n_in_hc0[v]--;
						if(var_n_in_hc0[v] == 0)
						{
							ptr_to_vhc0->delete_element(v);
						}					
					}
					ptr_to_hc0->delete_element(c);
					if(weight[c] > 1 && !ptr_to_hcw2sat->element_in(c))
					{
						ptr_to_hcw2sat->insert_element(c);
					}
				}
				else
				{
					for(lit* p = clause_c; (v = p->var_num) != 0; p++) 
					{
						if(v != flipvar)
							sscore[v] -= weight[c];						
					}
					ptr_to_sc0->delete_element(c);				
					sweight_unsat -= weight[c];
				}
			}
		}
		else // value[flipvar] != cur_lit.sense
		{
			--sat_n[c];
			if(sat_n[c] == 1) //sat_n from 2 to 1
			{	
				for(lit* p = clause_c; (v = p->var_num) != 0; p++) 
				{
					if(p->sense == value[v])
					{
						if(isHard[c])
						{
							hscore[v] -= weight[c];
						}
						else
						{
							sscore[v] -= weight[c];
						}
						sat_var[c] = v;											
						break;
					}
				}
			}
			else if(sat_n[c] == 0) //sat_n from 1 to 0
			{
				if(isHard[c])
				{
					for(lit* p = clause_c; (v = p->var_num) != 0; p++) 
					{
						if(v != flipvar)
						{
							hscore[v] += weight[c];
						}
						var_n_in_hc0[v]++;
						if(var_n_in_hc0[v] == 1)
						{
							ptr_to_vhc0->insert_element(v);
						}
					}
					ptr_to_hc0->insert_element(c);

					if(ptr_to_hcw2sat->element_in(c))
					{
						ptr_to_hcw2sat->delete_element(c);
					}
					
				}
				else
				{
					for(lit* p = clause_c; (v = p->var_num) != 0; p++) 
					{
						if(v != flipvar)
							sscore[v] += weight[c];
					}
					ptr_to_sc0->insert_element(c);			
					sweight_unsat += weight[c];
				}
			}			
		}//end else
	}
#ifdef debug_mode
//cout << 2 << endl;
#endif
	sscore[flipvar] = -org_flipvar_sscore;
	hscore[flipvar] = -org_flipvar_hscore;
#ifdef debug_mode

#endif
	update_hd_and_h0sd(flipvar);
#ifdef debug_mode
//cout << "right after dealing with flipvar " << flipvar << ": " << endl;
//show_hd();
#endif
	int *p;
	for(p = var_neighbor[flipvar]; (v = *p) != 0; p++)
	{
#ifdef debug_mode
//cout << "considering " << v << " for update hd and h0sd" << endl;
#endif
		update_hd_and_h0sd(v);
#ifdef debug_mode
//cout << "right after dealing with var " << v << ": " << endl;
//show_hd();
#endif
	}
#ifdef debug_mode
//cout << "at the end of flip_3SAT" << endl;
//show_hd();
#endif	
#ifdef last_second_flip_time_mode
		last_second_flip_time[flipvar] = last_flip_time[flipvar];
#endif
		last_flip_time[flipvar] = step;
#ifdef debug_mode
if(!check_vhc0()) exit(1);
#endif
}

void (* flip)(int);//refer to update_sscore_clause(int flipvar) or update_sscore_pscore_clause(int flipvar)


void update_hard_clause_weight_with_paws()
{
	int i;
	int v, c;
#ifdef debug_mode
//cout << "about to update the hard clause weights" << endl;
//print_score();
#endif
	if(rand() % 1000000 < sp_value)//
	{
#ifdef debug_mode
//cout << "about to smooth" << endl;
#endif
		// smoothing
		for(i = ptr_to_hcw2sat->begin(); i < ptr_to_hcw2sat->end(); )// for those clauses whose weight is at least 2
		{
#ifdef debug_mode
//cout << "smoothing" << endl;
#endif
			c = ptr_to_hcw2sat->at(i);
			weight[c]--;
				
			if(weight[c] == 1)
			{
				ptr_to_hcw2sat->delete_element(c);
			}
			else 
				i++;// just to consider the next one

			if(sat_n[c] == 1)// for 1-satisfied clauses
			{
				// update the respective hscore
				v = sat_var[c];
				hscore[v]++;
				// update hd and h0sd
				update_hd_and_h0sd(v);
			}
		}
	}		
	else 
	{
#ifdef debug_mode
//cout << "about to increase unsat hard weights" << endl;
//cout << "num of unsat hard clauses: " << ptr_to_hc0->size() << endl;
//getchar();
#endif
		// only increasing the weights of the violated clauses
		for(i = ptr_to_hc0->begin(); i < ptr_to_hc0->end(); ++i)
		{
			c = ptr_to_hc0->at(i);
#ifdef debug_mode
cout << "considering the hard unsat clause " << c << endl;
#endif
			weight[c]++;
#ifdef debug_mode
cout << "the weight of the hard unsat clause " << c << " is updated to be " << weight[c] << endl;
getchar();
#endif	
#ifdef debug_mode
/*

*/
#endif
		}
#ifdef debug_mode
//show_vhc0();
#endif		
		for(i = ptr_to_vhc0->begin(); i < ptr_to_vhc0->end(); ++i)// for all variables that occur in violated clauses
		{
			v = ptr_to_vhc0->at(i);
#ifdef debug_mode
//cout << "considering the variable " << v << " in unsat hard clauses." << endl;
#endif
			hscore[v] += var_n_in_hc0[v];// var_n_cv0[v] is the number of violated clauses that v occurs in
						// because the weights of all such clauses are increased by 1, the score of v should be updated accordingly
#ifdef debug_mode
//cout << "the hscore of the variable " << v << " is updated to be " << hscore[v] << endl;
#endif		
			update_hd_and_h0sd(v);
		}
	}
#ifdef debug_mode
if(!check_score()) exit(1);
//getchar();
#endif	
}


///p3
int pick_var_3SAT()
{
#ifdef debug_mode
//cout << "having just entering pick_var_3SAT" << endl;
#endif
	int i, c, v;
	int ret_v;
//hard decreasing mode
	if(ptr_to_hd->size())
	{
#ifdef debug_mode
//cout << "hard decreasing mode" << endl;
//if(!check_vhc0()) exit(1);
//cout << "ptr_to_hd->size(): " << ptr_to_hd->size() << endl;
//show_hd();
#endif
#ifdef rand_hard_decreasing_mode
		ret_v = ptr_to_hd->at(rand() % ptr_to_hd->size() + 1);
		return ret_v;
#endif
		v = ptr_to_hd->at(1);
		best_cand_vars[0] = v;
		best_cand_var_n = 1;
#ifdef debug_mode
//cout << v << " enters best_cand_vars " << endl;
//cout << "hscore[" << v << "]: " << hscore[v] << endl;
//cout << "sscore[" << v << "]: " << sscore[v] << endl;
#endif
		if(sweight_unsat < sweight_unsat_best)// soft-cost < soft-cost*
		{
			best_score_value = hscore[v];
			for(i = 2; i <= ptr_to_hd->size(); i++)
			{
				v = ptr_to_hd->at(i);
#ifdef debug_mode
//cout << "considering hscore[" << v << "]: " << hscore[v] << endl;
#endif
				if(hscore[v] > best_score_value)
				{
#ifdef debug_mode
//cout << "clear best_cand_vars, and then " << v << " enters best_cand_vars " << endl;
#endif
					best_cand_vars[0] = v;
					best_cand_var_n = 1;
					best_score_value = hscore[v];
				}
				else if(hscore[v] == best_score_value)
				{
#ifdef debug_mode
//cout << v << " enters best_cand_vars " << endl;
#endif
					best_cand_vars[best_cand_var_n++] = v;
				}
			}
		}
		else// soft-cost >= soft-cost*
		{
			best_score_value = sscore[v];
			for(i = 2; i <= ptr_to_hd->size(); i++)
			{
				v = ptr_to_hd->at(i);
#ifdef debug_mode
//cout << "considering sscore[" << v << "]: " << sscore[v] << endl;
#endif
				if(sscore[v] > best_score_value)
				{
#ifdef debug_mode
//cout << "clear best_cand_vars, and then " << v << " enters best_cand_vars " << endl;
#endif
					best_cand_vars[0] = v;
					best_cand_var_n = 1;
					best_score_value = sscore[v];
				}
				else if(sscore[v] == best_score_value)
				{
#ifdef debug_mode
//cout << v << " enters best_cand_vars " << endl;
#endif
					best_cand_vars[best_cand_var_n++] = v;
				}
			}
		}
#ifdef debug_mode
show_best_cand_vars();
#endif
		ret_v = best_cand_vars[rand() % best_cand_var_n];
		return ret_v;
	}
//soft decreasing mode
	if(ptr_to_h0sd->size())
	{
#ifdef debug_mode
//cout << "soft decreasing mode" << endl;
//show_h0sd();
#endif
		v = ptr_to_h0sd->at(1);
		best_cand_vars[0] = v;
		best_cand_var_n = 1;
		best_score_value = sscore[v];
		for(i = 2; i <= ptr_to_h0sd->size(); i++)
		{
			v = ptr_to_h0sd->at(i);
			if(sscore[v] > best_score_value)
			{
				best_cand_vars[0] = v;
				best_cand_var_n = 1;
				best_score_value = sscore[v];
			}
			else if(sscore[v] == best_score_value)
			{
				best_cand_vars[best_cand_var_n++] = v;
			}
		}
		ret_v = best_cand_vars[rand() % best_cand_var_n];	
		return ret_v;		
	}
//random mode
#ifdef debug_mode
//cout << "random mode" << endl;
#endif
	update_hard_clause_weight_with_paws();
	if(ptr_to_hc0->size())
	{
		c = ptr_to_hc0->at(rand() % ptr_to_hc0->size() + 1);
#ifdef debug_mode
//cout << "having just picked an unsat hard clause " << c << endl;
//getchar();
#endif
	}
	else
	{
		c = ptr_to_sc0->at(rand() % ptr_to_sc0->size() + 1);
#ifdef debug_mode
//cout << "having just picked an unsat soft clause " << c << endl;
//getchar();
#endif
	}

	lit *p = clause_lit[c];
	if(rand() % 10000 < 100) //with probability 1%
	{
		ret_v = (p + (rand() % clause_lit_count[c])) -> var_num;
	}
	else
	{
		v = p->var_num;
		best_cand_vars[0] = v;
		best_cand_var_n = 1;
		best_score_value = sscore[v];
		p++;
#ifdef debug_mode
//cout << v << " enters best_cand_vars" << endl;
//cout << "soft score of " << v << " is " << sscore[v] << endl;
#endif	
		while((v = p->var_num) != 0)
		{
#ifdef debug_mode
//cout << v << " being considered" << endl;
//cout << "soft score of " << v << " is " << sscore[v] << endl;
#endif
			if(sscore[v] > best_score_value)
			{
				best_cand_vars[0] = v;
				best_cand_var_n = 1;
				best_score_value = sscore[v];
			}
			else if(sscore[v] == best_score_value)
			{
				best_cand_vars[best_cand_var_n++] = v;
			}
			p++;
		}
#ifdef debug_mode
//show_best_cand_vars();
#endif
		ret_v = best_cand_vars[rand() % best_cand_var_n];
#ifdef debug_mode
//cout << "will return " << ret_v << " for random walk" << endl;
//getchar();
#endif
	}
	return ret_v;
}

#endif
