/*
 * absys.c
 *
 *  Created on: May 5, 2014
 *      Author: nguyen
 */
#include "abssys.h"
#define MAX_ABS 10
extern System original;
extern Eqlist eql;
Symbol pat;
extern Term TERM_NIL;
extern struct switchdata switches;
static List absList;
List outputClaims;
List falsifiedClaims;
List verified, falsified;
Termlist secret;
Termlist secretav;
Termlist claims;
int abstcount;

void initKnowledge()
{
	knowledgeAddTerm(original->know,TERM_NIL);
}

void initClaims()
{
	claims=NULL;
	Claimlist cl;
	for(cl= original->claimlist; cl!=NULL; cl=cl->next)
	{
		if(!isClaimSignal(cl)&&!cl->alwaystrue)
		claims = termlistAppend(claims,cl->label);
	}
}
void abssysInit(){
	outputClaims=falsifiedClaims=NULL;
	absList = NULL;
	secret= NULL;
	pat = symbolSysConst("Pat_");
	initKnowledge();
	initClaims();
}

void addProt2Stack (const void *data)
{
  List newnode;

  newnode = list_create (data);
  if (absList == NULL)
  {
	  absList = newnode;
  }
  else
  {
	  newnode->next = absList;
	  absList->prev = newnode;
  }
  absList = newnode;
}
void buildAbstractionList()
{
	System abssys = original;
	abstcount=0;
	do
	{
		abssys = abstractSystem(abssys);
		if(abstractionSucceed())
		{
			addProt2Stack(abssys);
			eprintf("Abstraction number %d:\n",++abstcount);
			protocolsPrint(abssys->protocols);
			eprintf("\n");
			//abstcount++;
		}
		else break;
	}
	while(abstcount<MAX_ABS);
	eprintf("Number of abstractions:%d\n",abstcount);
}

void outputResult(System abssys)
{
	List claims = verified;
	while(claims!=NULL)
	{
		claimStatusReport (abssys, claims->data);
		if (switches.xml)
		{
		  xmlOutClaim (abssys, claims->data);
		}
		claims = claims->next;
	}
	/*
	Claimlist claims = abssys->claimlist;
	while(claims!=NULL)
	{
		claimStatusReport (abssys, claims);
		if (switches.xml)
		{
		  xmlOutClaim (abssys, claims);
		}
		claims = claims->next;
	}
	*/
}

void freeClaims()
{
	while(verified!=NULL)
	{
		List tmp = verified;
		verified=verified->next;
		free(tmp);
	}

	while(falsified!=NULL)
	{
		List tmp = falsified;
		falsified=falsified->next;
		free(tmp);
	}

}
void freeSystem(System sys)
{
  knowledgeDelete(sys->know);//only shallow deletion is done because abstract systems share the basic knowledge
  protocolDelete(sys->protocols);
  systemDone (sys);
}

void addSecretTerms()
{
	Claimlist cl= original->claimlist;
	while(cl!=NULL)
	{
		if(isSecretClaim(cl))
		{
			secret = termlistAdd(secret,cl->parameter);
		}
		cl = cl->next;
	}
}


Roledef findEventContainTerm(Roledef rd, Term t)
{
	while(rd!=NULL)
	{
		if(rd->type!=CLAIM&&containTermInPlain(t,rd->message))
			return rd;
		rd= rd->next;
	}
	return NULL;
}
/*
Term getImage(Term t, Termlist subs)
{
	Termlist tl = subs;
	while(tl!=NULL)
	{
		if(isTermEqual(t,tl->term)) return tl->term->subst;
		tl = tl->next;
	}
	return NULL;
}

Term getPreImage(Term t, Termlist subs)
{
	Termlist tl = subs;
	while(tl!=NULL)
	{
		if(isTermEqual(t,tl->term->subst)) return tl->term;
		tl = tl->next;
	}
	return t;
}


Term buildSecretTerm(Term t, Termlist subs)
{
	if(realTermLeaf(t))
	{
		if(t->type==GLOBAL) return t;
		Term img = getImage(t,subs);
		t=img==NULL?t:img;
		return t;
	}
	Term preimg = getPreImage(t,subs);
	if(preimg!=NULL) return preimg;
	if(realTermEncrypt(t))
	{
		Term op = buildSecretTerm(TermOp(t), subs);
		if(t->helper.fcall)
			return makeTermFcall(op, TermKey(t));
		else return makeTermEncrypt(op,buildSecretTerm(TermKey(t),subs));
	}
	return makeTermTuple(buildSecretTerm(TermOp1(t), subs),buildSecretTerm(TermOp2(t), subs));
}

*/
void addSecretTerm(Termlist tl)
{
	Termlist tmp;
	for(tmp=tl; tmp!=NULL; tmp = tmp->next)
	{
		if(isSubtermInTermlist(tmp->term,secret))
		{
			if(!termInList(secret,tmp->term->subst))
				secret = termlistAdd(secret,tmp->term->subst);
		}
		else if(isSubtermInTermlist(tmp->term->subst,secret))
		{
			if(!termInList(secret,tmp->term))
				secret = termlistAdd(secret,tmp->term);
		}
	}
}
void secrecyAnalysis(Role roles, Role r, Term sec)
{
	Termlist av = extractAV(NULL,sec,0);
	Termlist tl=av;
	Termlist subs=NULL;
	Termlist av1=NULL;
	while(tl!=NULL)
	{
		Roledef rd = findEventContainTerm(r->roledef,tl->term);
		if(rd!=NULL)
		{
			Roledef rd1 = findSendRecvEvent(roles,rd);
			if(rd1!=NULL)
			{
				Termlist st = termMguTerm(rd->message, rd1->message);
				if(st!=MGUFAIL)
				{
					subs = termlistConcat(st,subs);
				}
			}
			Termlist tmp = extractAV(NULL,rd->message,0);
			av1 = termlistConcat(tmp,av1);
			if(termlistContained(av1,av)) break;
		}
		tl=tl->next;
	}
	/*
	Term secterm = buildSecretTerm(sec,subs);
	termlistSubstReset(subs);
	if(!inTermlist(secret,secterm))
		secret = termlistAdd(secret,secterm);
	*/
	addSecretTerm(subs);
	termlistSubstReset(subs);
	termlistDelete(subs);
	termlistDelete(av);
}

void declareSecrets()
{
	addSecretTerms();
	Role r;
	Roledef rd;
	Protocol main_prot = original->protocols;
	while(main_prot!=NULL&&isHelperProtocol(main_prot))
		main_prot=main_prot->next;
	for(r = main_prot->roles; r!=NULL;r=r->next)
	{
		for(rd = r->roledef;rd!=NULL;rd=rd->next)
			if(rd->type==CLAIM&&isSecretClaim(rd->claiminfo))
				secrecyAnalysis(main_prot->roles,r,rd->message);
	}
	//extract atoms and variables from secrets
	Termlist tl = NULL;
	Termlist tmp;
	for(tmp = secret; tmp!=NULL; tmp= tmp->next)
		tl = extractAV(tl,tmp->term,0);
	//termlistDelete(secret);
	secret = tl;
	secretav=tl;
}

void list_delete_system(List l)
{
	while(l!=NULL)
	{
		List tmp = l;
		l = l->next;
		freeSystem(tmp->data);
		free(tmp);
	}
}


int isRemovedClaim(Term label)
{
	List tmp;
	for(tmp=verified; tmp!=NULL; tmp = tmp->next)
	{
		Claimlist remove = (Claimlist)tmp->data;
		if(isTermEqual(remove->label, label))
			return 1;
	}

	for(tmp=falsified; tmp!=NULL; tmp = tmp->next)
	{
		Claimlist remove = (Claimlist)tmp->data;
		if(isTermEqual(remove->label, label))
			return 1;
	}

	return 0;
}
void removeVerifiedClaims()
{
	Termlist newClaims = NULL;
	Termlist labels;
	for(labels=claims; labels!=NULL;labels=labels->next)
	{
		if(!isRemovedClaim(labels->term))
			newClaims = termlistAdd(newClaims,labels->term);
	}
	termlistDelete(claims);
	claims=newClaims;
}

void runVerification(void (*MC_single)(const System))
{
	abssysInit();
	declareSecrets();
	addProt2Stack(original);
	  struct timeval start, finish;
	  long msec;
	  gettimeofday(&start, NULL);
	buildAbstractionList();
	  gettimeofday(&finish, NULL);
	  msec = timevaldiff(&start, &finish);
	eprintf("Constructing abstractions in milliseconds: %d\n",msec);
	System abssys;
	List abst = absList;
 	while(claims!=NULL&&abstcount>=0)
	{
		abssys = (System)abst->data;
	    //systemStart(abssys);
	    //abssys->traceKnow[0] = abssys->know;
		MC_single (abssys);
		//eprintf("Abstraction number %d: \n", abstcount);
		if(verified!=NULL||falsified!=NULL)
		{
			if(verified!=NULL)
			{
				if(abstcount)
				{
					//eprintf("Abstraction number %d:\n", abstcount);
					//protocolsPrint(abssys->protocols);
					//eprintf("\n");
					eprintf("Properties verified at abstraction number %d: \n",abstcount);
				}
				else
				eprintf("Properties verified at the original protocol:\n");
				outputResult(abssys);
			}
			removeVerifiedClaims();
		}
		abstcount--;
		freeClaims();
		verified=falsified=outputClaims=falsifiedClaims=NULL;
		abst = abst->next;
	}
 	list_delete_system(absList);
	deleteEqlist(eql);
	termlistDelete(secret);
	termlistDelete(secretav);
}

/*
 * stop once an attack is found
 *
*/
/*
void runVerification(int (*MC_single)(System))
{
	declareSecrets();
	addProt2Stack(sys);
	  struct timeval start, finish;
	  long msec;
	  gettimeofday(&start, NULL);
	buildAbstractionList();
	  gettimeofday(&finish, NULL);
	  msec = timevaldiff(&start, &finish);
	eprintf("Constructing abstractions in milliseconds: %d\n",msec);
	System abssys;
	List abst = absList;
 	while(claims!=NULL&&abstcount>=0)
	{
		abssys = (System)abst->data;
	    systemStart(abssys);
	    abssys->traceKnow[0] = abssys->know;
		//eprintf("Abstraction number %d: \n", abstcount);
		MC_single (abssys);
		protocolsPrint(abssys->protocols);
		eprintf("\n");
		outputResult(abssys);
		break;
		if(head!=NULL)
		{
			if(abstcount)
			{
				protocolsPrint(abssys->protocols);
				eprintf("\n");
				eprintf("Properties verified at abstraction number %d: \n",abstcount);
			}
			else
				eprintf("Properties verified at the original protocol:\n");
			outputResult(abssys);
			removeVerifiedClaims();
		}
		abstcount--;
		freeClaims();
		head=outputClaims=NULL;
		abst = abst->next;
	}
 	list_delete_system(absList);
	deleteEqlist(eql);
	termlistDelete(secret);
	termlistDelete(secretav);
}
*/
