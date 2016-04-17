#ifndef _DEBUG_H_
#define _DEBUG_H_

#include "basis.h"

int check_score();
void show_hd();
void show_h0sd();
int check_hd();
int check_h0sd();
void show_hc0();
void show_sc0();
int check_hc0();
int check_sc0();
int check_hcw2sat();
int check_vhc0();
void show_vhc0();
int check_value_valid();
int check_cand_solution();

int check_score()
{
cout << "check_score()..." << endl;
	int i, v, c;
	int lit_count;

	LL* ss = new LL[var_n+2];
	LL* hs = new LL[var_n+2];
	memset(ss, 0, (var_n + 2) * sizeof(LL));
	memset(hs, 0, (var_n + 2) * sizeof(LL));

	for(v = 1; v <= var_n; v++) 
	{
		ss[v] = 0;
		hs[v] = 0;
		lit_count = var_lit_count[v];
		
		for(i = 0; i < lit_count; ++i)
		{
			c = var_lit[v][i].clause_num;
			if(isHard[c])
			{
				if(sat_n[c] == 0)
				{
					hs[v] += weight[c];
				}
				else if(sat_n[c] == 1 && var_lit[v][i].sense == value[v]) {hs[v] -= weight[c];}
			}
			else
			{
				if(sat_n[c] == 0) ss[v] += weight[c];
				else if(sat_n[c] == 1 && var_lit[v][i].sense == value[v]) ss[v] -= weight[c];			
			}
		}
	}

	for(v = 1; v <= var_n; v++)
	{
//cout << "hscore[" << v << "] = " << hscore[v] << endl;
//cout << "hs[" << v << "] = " << hs[v] << endl;
//cout << "sscore[" << v << "] = " << sscore[v] << endl;
//cout << "ss[" << v << "] = " << ss[v] << endl;
		if(hscore[v] != hs[v])
		{
			cout << "hard score of " << v << " seems incorrect." << endl;
			delete[] hs; delete[] ss;
			return 0;
		}
		if(sscore[v] != ss[v])
		{
			cout << "soft score of " << v << " seems incorrect." << endl;
			delete[] hs; delete[] ss;
			return 0;
		}
	}
	delete[] hs; delete[] ss;
	return 1;
}
void show_hc0()
{
	cout << "hc0: " << endl;
	for(int i = ptr_to_hc0->begin(); i < ptr_to_hc0->end(); i++)
		cout << ptr_to_hc0->at(i) << '\t';
	cout << endl;
}
int check_hc0()
{
cout << "check_hc0()..." << endl;
	if(ptr_to_hc0->size() < 0)
	{
		cout << "the size of hc0 is illegal" << endl;
		return 0;		
	}
	for(int i = ptr_to_hc0->begin(); i < ptr_to_hc0->end(); i++)
		if(!isHard[ptr_to_hc0->at(i)] || sat_n[ptr_to_hc0->at(i)] != 0)
		{
			cout << "index " << i << ", clause " << ptr_to_hc0->at(i) << ", not an unsat hard clause" << endl;
		 	return 0;
		}
	for(int c = 0; c < clause_n; c++)
		if(isHard[c] && sat_n[c] == 0 && !ptr_to_hc0->element_in(c))
		{
			cout << "clause " << c << " is an unsat hard clause but not in hc0" << endl;
			return 0;
		}
	return 1;
}
void show_sc0()
{
	cout << "sc0: " << endl;
	for(int i = ptr_to_sc0->begin(); i < ptr_to_sc0->end(); i++)
		cout << ptr_to_sc0->at(i) << '\t';
	cout << endl;
}
int check_sc0()
{
cout << "check_sc0()..." << endl;
	if(ptr_to_sc0->size() < 0)
	{
		cout << "the size of sc0 is illegal" << endl;
		return 0;		
	}
	for(int i = ptr_to_sc0->begin(); i < ptr_to_sc0->end(); i++)
		if(isHard[ptr_to_sc0->at(i)] || sat_n[ptr_to_sc0->at(i)] != 0)
		{
			cout << "index " << i << ", clause " << ptr_to_sc0->at(i) << ", not an unsat soft clause" << endl;
			return 0;
		}
	for(int c = 0; c < clause_n; c++)
		if(!isHard[c] && sat_n[c] == 0 && !ptr_to_sc0->element_in(c))
		{
			cout << "clause " << c << " is an unsat soft clause but not in sc0" << endl;
			return 0;
		}
	return 1;
}
void show_hd()
{
	cout << "the current hd structure: " << endl;
	cout << "variables: " << endl;
	for(int i = ptr_to_hd->begin(); i < ptr_to_hd->end(); i++)
		cout << ptr_to_hd->at(i) << '\t';
	cout << endl;
	cout << "hard scores: " << endl;
	for(int i = ptr_to_hd->begin(); i < ptr_to_hd->end(); i++)
		cout << hscore[ptr_to_hd->at(i)] << '\t';
	cout << endl;
}
int check_hd()
{
cout << "check_hd()..." << endl;
	if(ptr_to_hd->size() < 0)
	{
		cout << "the size of hd is illegal" << endl;
		return 0;
	}
	for(int i = ptr_to_hd->begin(); i < ptr_to_hd->end(); i++)
		if(hscore[ptr_to_hd->at(i)] <= 0)
		{
			cout << "ptr_to_hd->at(" << i << ")'s hard score is not positive." << endl;
			cout << "the variable at this location is " << ptr_to_hd->at(i) << endl;
			return 0;
		}
	for(int v = 1; v <= var_n; v++)
		if(hscore[v] > 0 && !ptr_to_hd->element_in(v))
		{
			cout << v << " should be in hd, but it is not." << endl; 
			return 0;
		} 
	return 1;
}
void show_h0sd()
{
	cout << "the current h0sd structure: " << endl;
	for(int i = ptr_to_h0sd->begin(); i < ptr_to_h0sd->end(); i++)
		cout << ptr_to_h0sd->at(i) << '\t';
	cout << endl;
	cout << "hard scores: " << endl;
	for(int i = ptr_to_h0sd->begin(); i < ptr_to_h0sd->end(); i++)
		cout << hscore[ptr_to_h0sd->at(i)] << '\t';
	cout << endl;
	cout << "soft scores: " << endl;
	for(int i = ptr_to_h0sd->begin(); i < ptr_to_h0sd->end(); i++)
		cout << sscore[ptr_to_h0sd->at(i)] << '\t';
	cout << endl;
}
int check_h0sd()
{
cout << "check_h0sd()..." << endl;
	if(ptr_to_h0sd->size() < 0)
	{
		cout << "the size of h0sd is illegal" << endl;
		return 0;
	}
	for(int i = ptr_to_h0sd->begin(); i < ptr_to_h0sd->end(); i++)
	{
		if(hscore[ptr_to_h0sd->at(i)] != 0)
		{
			cout << "ptr_to_h0sd->at(" << i << ")'s hard score is not 0." << endl;
			cout << "the variable at this location is " << ptr_to_h0sd->at(i) << endl;
			return 0;
		}
		else if(sscore[ptr_to_h0sd->at(i)] <= 0)
		{
			cout << "ptr_to_h0sd->at(" << i << ")'s soft score is not positive." << endl;
			cout << "the variable at this location is " << ptr_to_h0sd->at(i) << endl;
			return 0;
		}
	}
	for(int v = 1; v <= var_n; v++)
	{
		if(hscore[v] == 0 && sscore[v] > 0 && !ptr_to_h0sd->element_in(v))
		{
			cout << v << " should be in h0sd, but it is not." << endl; 
			return 0;
		}
	}
	return 1;
}
int check_hcw2sat()
{
cout << "check_hcw2sat()..." << endl;
	int i, c;
	if(ptr_to_hcw2sat->size() < 0)
	{
		cout << "the size of hcw2sat is illegal" << endl;
		return 0;
	}
	for(i = ptr_to_hcw2sat->begin(); i < ptr_to_hcw2sat->end(); i++)
	{
		c = ptr_to_hcw2sat->at(i);
		if(!isHard[c])
		{
			cout << "checking hcw2sat:" << endl;
			cout << "at " << i << ", " << c << " is not hard." << endl;
			return 0;
		}
		if(weight[c] < 2)
		{
			cout << "checking hcw2sat:" << endl;
			cout << "at " << i << ", " << c << " is of weight 1." << endl;
			return 0;
		}
		if(sat_n[c] == 0)
		{
			cout << "checking hcw2sat:" << endl;
			cout << "at " << i << ", " << c << " is unsat." << endl;
			return 0;
		}
	}
	for(c = 0; c < clause_n; c++)
	{
		if(isHard[c] && weight[c] > 1 && sat_n[c] > 0 && !ptr_to_hcw2sat->element_in(c))
		{
			cout << "checking hcw2sat:" << endl;
			cout << c << " is an unsat hard clause with weight greater than 1, but not in hcw2sat" << endl;
			return 0;			
		}
	}
	return 1;
}
int check_vhc0()
{
#ifdef debug_mode
cout << "checking_vhc0()..." << endl;
#endif
	int i; 
	int u, v;
	int c;
	lit* p;
	int unsat_occur_num;
	int isFirstTime = 1;
	for(i = ptr_to_vhc0->begin(); i < ptr_to_vhc0->end(); i++)
	{
		v = ptr_to_vhc0->at(i);
		unsat_occur_num = 0;
		if(var_n_in_hc0[v] <= 0)
		{
			cout << "ptr_to_vhc0->at(" << i << ") is inconsistent with var_n_in_hc0" << endl;
			return 0;
		}
		for(c = 0; c < clause_n; c++)
		{
			if(isHard[c] && sat_n[c] == 0)
			{
				for(p = clause_lit[c]; (u = p->var_num) != 0; p++)
				{
					if(isFirstTime)
					{
						if(!ptr_to_vhc0->element_in(u))
						{
							cout << u << " occurs in usat hard clauses, but not in vhc0" << endl;
							return 0;
						}
					}
					if(u == v) unsat_occur_num++;
				}
			}
		}
		if(unsat_occur_num != var_n_in_hc0[v])
		{
			cout << "the number of occurrences of " << v << " in unsat clauses is inconsistent with var_n_in_hc0" << endl;
			return 0;
		}
		isFirstTime = 0;
	}
	return 1;
}
void show_vhc0()
{
	cout << "showing vhc0:" << endl;
	for(int i = ptr_to_vhc0->begin(); i < ptr_to_vhc0->end(); i++)
	{
		cout << ptr_to_vhc0->at(i) << '\t';
	}
	cout << endl;
	cout << "num of occurrences:" << endl;
	for(int i = ptr_to_vhc0->begin(); i < ptr_to_vhc0->end(); i++)
	{
		cout << var_n_in_hc0[ptr_to_vhc0->at(i)] << '\t';
	}
	cout << endl;
}
int check_cand_solution()
{
cout << "check_cand_solution()..." << endl;
	LL ss = 0;
	int hc0_n = 0;
	int c, flag, j;
	
	for (c = 0; c < clause_n; ++c) 
	{
		flag = 0;
		for(j = 0; j < clause_lit_count[c]; ++j)
		{
			//cout << "value[clause_lit[" << c << "][" << j << "].var_num]: " << value[clause_lit[c][j].var_num] << endl;
			//cout << "clause_lit[" << c << "][" << j << "].sense]: " << clause_lit[c][j].sense << endl;
			//cout << endl;
			if (value[clause_lit[c][j].var_num] == clause_lit[c][j].sense) {flag = 1; break;}
		}

		if(flag == 0){//the clause is unsatisfied by the solution
			if(isHard[c])
			{
				//cout << "hard clause " << c << " is unsat" << endl;
				hc0_n++;
			}
			else ss += weight[c];			
		}
	}
	if(hc0_n != ptr_to_hc0->size())
	{
		cout << "hc0_n: " << hc0_n << endl;
		cout << "ptr_to_hc0->size(): " << ptr_to_hc0->size() << endl;
		cout << "ptr_to_hc0->size() is computed incorrectly" << endl;
		return 0;
	}
	if(ss != sweight_unsat)
	{
		cout << "sweight_unsat is computed incorrectly" << endl;
		return 0;
	}
	return 1;
}

int check_value_valid()
{
cout << "check_value_valid()..." << endl;
	for(int v = 1; v <= var_n; v++)
	{
		if(value[v] != 0 && value[v] != 1)
		{
			cout << "illegally write to the value of variable " << v << endl;
			return 0;
		}
	}
	return 1;
}


void print_solution()
{
     int i;

     cout << "v ";
     for(i = 1; i <= var_n; i++) {
         if(value[i] == 0) cout << "-";
         cout << i;
         if(i % 10 == 0) cout << endl << "v ";
         else cout << '\t';
     }
     cout << "0" << endl;
}

void print_score()
{
	int i;
	cout << "h ";
	for(i = 1; i <= var_n; ++i){
		cout << hscore[i];
		if(i % 10 == 0) cout << endl << "h ";
		else cout << '\t';
	}
	cout << "*" << endl;
	cout << "s ";
	for(i = 1; i <= var_n; ++i){
		cout << sscore[i];
		if(i % 10 == 0) cout << endl << "s ";
		else cout << '\t';
	}
	cout << "*" << endl;
}

void show_best_cand_vars()
{
	cout << "best_cand_vars: " << endl;
	for(int i = 0; i < best_cand_var_n; i++)
	{
		cout << best_cand_vars[i] << '\t';
	}
	cout << endl;
}

int verify_sol()
//only check satisfiability, not for maxsat
{
	int c, j; 
	int flag;
	
	for(c = 0; c < clause_n; ++c) 
	{
		flag = 0;
		for(j = 0; j < clause_lit_count[c]; ++j)
			if(value[clause_lit[c][j].var_num] == clause_lit[c][j].sense) {flag = 1; break;}

		if(flag == 0){//output the clause unsatisfied by the solution
			cout << "clause " << c << " is not satisfied" << endl;
			
			for(j = 0; j < clause_lit_count[c]; ++j)
			{
				if(clause_lit[c][j].sense == 0) cout << "-";
				cout << clause_lit[c][j].var_num << " ";
			}
			cout << endl;
			
			for(j = 0; j < clause_lit_count[c]; ++j)
				cout << value[clause_lit[c][j].var_num] << " ";
			cout << endl;

			return 0;
		}
	}
	return 1;
}

int Check()
{
	LL s = 0;
	int c, flag, j;
	
	for (c = 0; c < clause_n; ++c) 
	{
		flag = 0;
		for(j = 0; j < clause_lit_count[c]; ++j)
			if (value_best[clause_lit[c][j].var_num] == clause_lit[c][j].sense) {flag = 1; break;}

		if(flag == 0){//the clause is unsatisfied by the solution
			if(isHard[c]) return 0;
			else s += weight[c];			
		}
	}
	
	if(s != sweight_unsat_best)
	{
		return 0;
	}
	return 1;
}

void Write_answer()//output the best answer
{
	int v;
	printf("v");

	for(v = 1; v <= var_n; v++)
	{
		putchar(' ');
		if(!value_best[v])
			putchar('-');
		printf("%d", v);
	}	
	puts("");
}
#endif
