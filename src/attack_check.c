/*
 * attack_check.c

 *
 *  Created on: Mar 9, 2015
 *      Author: nguyen
 */
#include "attack_check.h"
extern System original;
extern Protocol INTRUDER;
int tracelength;
int regular_runs;

Runinfo runs;
int maxruns;

void initModelCheck(System sys)
{
	  systemStart (sys);
	  sys->traceKnow[0] = sys->know;	// store initial knowledge
	  bindingInit (sys);
	  arachneInit (sys);
	  systemReset (sys);		// reset any globals
	  systemRuns (sys);		// init runs data
}

struct runinfo copyRun(struct run r)
{
	struct runinfo result;
	result.protocol = r.protocol;
	result.protocol = r.protocol;
	result.role = r.role;
	Roledef rd =roledef_shift(r.start,r.step-1);
	result.lastevent = rd->label;
	return result;
}

void copyRuns(System sys)
{
	 maxruns = 0;
	 runs = (Runinfo) realloc (runs, sizeof (struct runinfo) * (sys->maxruns));
	 int i;
	 for(i=0; i< sys->maxruns;i++)
	 {
		 if(sys->runs[i].protocol != INTRUDER)
		 {
			 runs[maxruns] = copyRun(sys->runs[i]);
			 maxruns++;
		 }
	 }
	 regular_runs = sys->num_regular_runs;
}

void mapRuns(Claimlist cl, int* newruns, int* newgoals)
{
	Protocol p;
	Role r;
	tracelength = 0;
	original->num_intruder_runs = 0;
	original->attackid=0;
	int i;
	for(i = 0; i< maxruns;i++)
	{
			Protocol abst_p = runs[i].protocol;
			for(p = original->protocols; p!=NULL;p=p->next)
				if(isTermEqual(p->nameterm, abst_p->nameterm))
				{
					Role abst_r = runs[i].role;
					for(r = p->roles; r!=NULL; r = r->next)
						if(isTermEqual(r->nameterm, abst_r->nameterm))
						{
							roleInstance(original, p, r, NULL, NULL);
							(*newruns)++;
							original->runs[i].height = 0;
							//identify how many steps that should be executed in the original model
							Roledef rd;
							int step = 1;
							for(rd = r->roledef; rd!=NULL && !isTermEqual(rd->label,runs[i].lastevent); rd= rd->next)
							{
								step++;
							}
							if(i==0)
								*newgoals=add_recv_goals(i, 0, step-1);
							else original->runs[i].step = step;
							tracelength+=step;
							break;
						}
					break;
				}
	}
	switches.maxtracelength = tracelength;
	switches.runs = regular_runs;
}


