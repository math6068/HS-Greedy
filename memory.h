#ifndef _MEMORY_H
#define _MEMORY_H

#include <iostream>
#include <fstream>
#include <cstdlib>
#include <cmath>

using namespace std;

#include "basis.h"

void free_memory()
{
	int i;
	for(i = 0; i < clause_n; i++) 
	{
		delete[] clause_lit[i];
	}
	
	for(i = 1; i <= var_n; ++i)
	{
		delete[] var_lit[i];
		delete[] var_neighbor[i];
	}
	
	delete[] var_lit;
	delete[] var_lit_count;
	delete[] clause_lit;
	delete[] clause_lit_count;
	delete[] sscore;
	delete[] hscore;
	delete[] last_flip_time;
#ifdef last_second_flip_time_mode
    delete[] last_second_flip_time;
#endif
	delete[] var_neighbor;
	delete[] var_neighbor_count;
	delete[] weight;
	delete[] sat_n;
	delete[] sat_var;
	delete[] best_cand_vars;
	delete ptr_to_h0sd;
	delete ptr_to_hd;
	delete[] var_n_in_hc0;
	delete ptr_to_vhc0;
	delete ptr_to_sc0;
	delete ptr_to_hc0;
	delete ptr_to_hcw2sat;
	delete[] isHard;
	delete[] ans;
	delete[] ans_in;
	delete[] value;
	delete[] value_best;
#ifdef bucket_mode
	//soft_partitions.destroyBucketsAndNodes();
#endif
}

/** Read the instance*/

int build_instance(char *filename)
{
	char    line[1024];
	char    tempstr1[10];
	char    tempstr2[10];
	int     cur_lit;
	int     i, j;
	int		v, c;//var, clause
	
	ifstream infile(filename);
	if(infile == NULL) return 0;

	/*** build problem data structures of the instance ***/
	do{
		infile.getline(line, 1024);
	}while(line[0] != 'p');
	
	int line_n = strlen(line);
	line[line_n++] = ' ';
	line[line_n++] = '0';//a character '0'
	line[line_n] = 0;//string end
	
	sscanf(line, "%s %s %d %d %lld", tempstr1, tempstr2, &var_n, &clause_n, &weight_hard);

	//time_limit -= var_n / print_speed;
	
	//zz
	var_lit = new lit*[var_n+2];
	var_lit_count = new int[var_n+2];
	clause_lit = new lit*[clause_n+2];
	clause_lit_count = new int[clause_n+2];

	sscore = new LL[var_n+2];
	hscore = new LL[var_n+2];

	last_flip_time = new LL[var_n+2];
#ifdef last_second_flip_time_mode
	last_second_flip_time= new LL[var_n+2];
#endif
	var_neighbor = new int*[var_n+2];
	var_neighbor_count = new int[var_n+2];
	weight = new LL[clause_n+2];
	sat_n = new int[clause_n+2];
	sat_var = new int[clause_n+2];

	best_cand_vars = new int[var_n+2];

	ptr_to_sc0 = new Bijection(clause_n + 2);
	ptr_to_hc0 = new Bijection(clause_n + 2);
	ptr_to_hcw2sat = new Bijection(clause_n + 2);
	isHard = new int[clause_n+2];

	ptr_to_hd = new Bijection(var_n + 2);
	ptr_to_h0sd = new Bijection(var_n + 2);

	var_n_in_hc0 = new int[var_n+2];
	ptr_to_vhc0 = new Bijection(var_n + 2);
	
	ans = new int[var_n+2];
	ans_in = new int[var_n+2];
	value = new int[var_n+2];
	value_best = new int[var_n+2];
	int* temp_lit = new int[var_n+2];		
	if(strcmp(tempstr2, "wcnf") == 0)
		flag_weighted = 1;

	memset(clause_lit_count, 0, (clause_n + 2) * sizeof(int));
	memset(var_lit_count, 0, (var_n + 2) * sizeof(int));

	//Now, read the clauses, one at a time.
	for(c = 0; c < clause_n; c++) 
	{
		if(flag_weighted)
		{
			infile >> weight[c];
			if(weight[c] == weight_hard)
			//when weight_hard == 0, i.e., no hard clauses exist, 
			//this condition never holds, i.e., all clauses should be marked as soft, 
			//the respective weights should be the same as given
			{
#ifdef debug_mode
//cout << "clause " << c << ", weight: " << weight[c] << endl;
//cout << "it is hard, change weight to be 1" << endl;
//getchar();
#endif
				isHard[c] = 1;
				weight[c] = 1;
			}
			else
			{
#ifdef debug_mode
//cout << "clause " << c << ", weight: " << weight[c] << endl;
//cout << "it is soft, keep weight unchanged" << endl;
//getchar();
#endif
				isHard[c] = 0;
			}
		}
		else
			weight[c] = 1;
		
		infile >> cur_lit;

		while (cur_lit != 0) { 
			temp_lit[clause_lit_count[c]] = cur_lit;
			clause_lit_count[c]++;	
			infile >> cur_lit;
		}
		
		clause_lit[c] = new lit[clause_lit_count[c] + 1];
		
		for(i = 0; i < clause_lit_count[c]; ++i)
		{
			clause_lit[c][i].clause_num = c;
			clause_lit[c][i].var_num = abs(temp_lit[i]);
			if (temp_lit[i] > 0) clause_lit[c][i].sense = 1;
				else clause_lit[c][i].sense = 0;			
			var_lit_count[clause_lit[c][i].var_num]++;
		}
		clause_lit[c][i].var_num = 0; //end flag
		clause_lit[c][i].clause_num = -1;//end flag
	}
	delete[] temp_lit;
	infile.close();
	
	//create var literal arrays
	for (v = 1; v <= var_n; ++v)
	{
		var_lit[v] = new lit[var_lit_count[v] + 1];
		var_lit_count[v] = 0;	//reset to 0, for build up the array
	}
	//scan all clauses to build up var literal arrays
	for (c = 0; c < clause_n; ++c) 
	{
		for(i = 0; i < clause_lit_count[c]; ++i)
		{
			v = clause_lit[c][i].var_num;
			var_lit[v][var_lit_count[v]] = clause_lit[c][i];
			++var_lit_count[v];
		}
	}
	for (v = 1; v <= var_n; ++v) //set boundary
		var_lit[v][var_lit_count[v]].clause_num = -1;

	build_neighbor_relation();

	//for smoothing
	if(var_n <= 2500) sp_value = 1000;
	else sp_value = 100;

	return 1;
}

void build_neighbor_relation()
{
	int	i, j, count;
	int v, c;

	int* neighbor_flap_use;
	int  neighbor_flap_use_n;
	int* neighbor_flag;

	neighbor_flap_use = new int[var_n+2];
	neighbor_flag = new int[var_n+2];
	
	memset(neighbor_flag, 0, sizeof(int) * (var_n + 2));
	neighbor_flap_use_n = 0;
	
	for(v = 1; v <= var_n; ++v)
	{
		var_neighbor_count[v] = 0;		
		neighbor_flag[v] = 1;
		neighbor_flap_use[neighbor_flap_use_n++] = v;//v itself entered
			
		for(i = 0; i < var_lit_count[v]; ++i)
		{
			c = var_lit[v][i].clause_num;
			for(j = 0; j < clause_lit_count[c]; ++j)
			{
				if(neighbor_flag[clause_lit[c][j].var_num] == 0)
				{
					var_neighbor_count[v]++;
					neighbor_flag[clause_lit[c][j].var_num] = 1;
					neighbor_flap_use[neighbor_flap_use_n++] = clause_lit[c][j].var_num;
				}
			}
		}
		var_neighbor[v] = new int[var_neighbor_count[v] + 1];
		count = 0;
		for(i = 1; i < neighbor_flap_use_n; ++i)
		{
				var_neighbor[v][count] = neighbor_flap_use[i];
				count++;
		}
		var_neighbor[v][count] = 0;		
		for(i = 0; i < neighbor_flap_use_n; ++i)
			neighbor_flag[neighbor_flap_use[i]] = 0;
		neighbor_flap_use_n = 0;
	}	
	//delete[] neighbor_flag; neighbor_flag = NULL;
	delete[] neighbor_flap_use;
	delete[] neighbor_flag;
}



#endif
