/*
 * Scyther : An automatic verifier for security protocols.
 * Copyright (C) 2007-2013 Cas Cremers
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
 */

#include <stdlib.h>
#include <stdio.h>
#include <limits.h>
#include <string.h>
#include "tac.h"
#include "term.h"
#include "termlist.h"
#include "label.h"
#include "system.h"
#include "knowledge.h"
#include "symbol.h"
#include "compiler.h"
#include "switches.h"
#include "specialterm.h"
#include "warshall.h"
#include "hidelevel.h"
#include "debug.h"
#include "intruderknowledge.h"
#include "error.h"
#include "mgu.h"
#include "type.h"
#include "bool.h"
#include "abstraction/typebasedabs.h"
/*
   Simple sys pointer as a global. Yields cleaner code although it's against programming standards.
   It is declared as static to hide it from the outside world, and to indicate its status.
   Other modules will just see a nicely implemented sys parameter of compile, so we can always change
   it later if somebody complains. Which they won't.
*/

static System sys;
static Tac tac_root;
Eqlist eql;
int nilfree;//0:nil-free, 1: initially not nil-free,2: permanently not nil-free
/*
 * Declaration from system.c
 */
extern int protocolCount;

/*
   Forward declarations.
*/

void tacProcess (Tac tc);
void levelInit (void);
void levelDone (void);
Term levelFind (Symbol s, int i);
Term symbolFind (Symbol s);
Term tacTerm (Tac tc);
Termlist tacTermlist (Tac tc);
Term levelDeclare (Symbol s, int isVar, int level);
void compute_role_variables (const System sys, Protocol p, Role r);
void roleKnows (Tac tc);

/*
 * Global stuff
 */

//! Levels of scope: global, protocol, role
#define MAXLEVELS 4 //change 3 to 4
#define CLAUSENUM 30
static Termlist leveltl[MAXLEVELS];
static Termlist *clauseVar;
static int level;
static int maxruns;

static Protocol thisProtocol;
static Role thisRole;

//! Init terms and such
void
compilerInit (const System mysys)
{
  int i;

  /* transfer to global static variable */
  sys = mysys;
  clauseVar = malloc(CLAUSENUM * sizeof(Termlist));
  /* init levels */
  for (i = 0; i < MAXLEVELS; i++)
    leveltl[i] = NULL;
  /* init clause variables */
  for(i=0; i<CLAUSENUM; i++)
	  clauseVar[i]=NULL;
  level = -1;
  levelInit ();
  /* create special terms */
  specialTermInit (sys);
  leveltl[MAXLEVELS-1] = termlistAdd(leveltl[MAXLEVELS-1], TERM_NIL);
}

//! Make a global constant
Term
makeGlobalConstant (const char *s)
{
  return levelDeclare (symbolSysConst (s), 0, 0);
}

//! Make a global variable
Term
makeGlobalVariable (const char *s)
{
  return levelDeclare (symbolSysConst (s), 1, 0);
}

//! Clean up afterwards
void
compilerDone (void)
{
  return;
}

//! Compute recv variables for a role
Termlist
compute_recv_variables (const Role r)
{
  Termlist tl;

  int process_event (Roledef rd)
  {
    if (rd->type == RECV)
      {
	tl = termlistAddVariables (tl, rd->from);
	tl = termlistAddVariables (tl, rd->to);
	tl = termlistAddVariables (tl, rd->message);
      }
    return 1;
  }

  tl = NULL;
  roledef_iterate_events (r->roledef, process_event);
  return tl;
}

/* ------------------------------------------------------------------- */

//! Compile the tac into the system
/**
 *@todo Currently, the semantics assume all labels are globally unique, but this is not enforced yet. There should be some automatic renaming when compositing protocols.
 *\sa oki_nisynch
 */

void checkingFuncspec(){
	int checkPatterndisjointness = checkPatternDisjointness();
	if(!checkPatterndisjointness) error("The function specification is not pattern-disjoint\n");
}

void
compile (Tac tc, int maxrunsset)
{
  /* Init globals */
  tac_root = tc;
  nilfree=0;
  eql=NULL;
  /* process the tac */
  tacProcess (tac_root);
  /* do some tests */
  /* Preprocess the result */
  preprocess (sys);
  /*do some checking for function specification */
  checkingFuncspec();
  /* cleanup */
  levelDone ();
}


//! Print error line number.
/**
 *@todo This is obsolete, and should all go to stderr
 */
void
errorTac (int lineno)
{
  globalError++;
  eprintf (" on line %i.\n", lineno);
  exit (1);
}

//! Enter nested scope.
void
levelInit (void)
{
  level++;
  if (level >= MAXLEVELS)
    {
      error ("level is increased too much.");
    }
  leveltl[level] = NULL;
}

//! Leave nested scope.
void
levelDone (void)
{
  if (level < 0)
    {
      error ("level is decreased too much.");
    }
  leveltl[level] = NULL;
  level--;
}

Term
levelDeclare (Symbol s, int isVar, int level)
{
  Term t;

  t = levelFind (s, level);
  if (t == NULL)
    {
      /* new! */
      if (isVar)
	{
	  t = makeTermType (VARIABLE, s, -(level + 1));
	  if(level<MAXLEVELS-1) sys->variables = termlistAdd (sys->variables, t);
	}
      else
	{
	  t = makeTermType (GLOBAL, s, -(level + 1));
	}
      leveltl[level] = termlistAdd (leveltl[level], t);

      /* add to relevant list */
      switch (level)
	{
	case 0:
	  sys->locals = termlistAdd (sys->locals, t);
	  break;
	case 1:
	  thisProtocol->locals = termlistAdd (thisProtocol->locals, t);
	  break;
	case 2:
	  thisRole->locals = termlistAdd (thisRole->locals, t);
	  break;
	}
    }
  return t;
}

//! Generate a term from a symbol
Term
symbolDeclare (Symbol s, int isVar)
{
  return levelDeclare (s, isVar, level);
}

int clauseVarFind(Symbol var, int clauseNum){
	  Termlist tl;
 int i;
 for(i=0; i<clauseNum;i++){
	  tl = clauseVar[i];
	  while (tl != NULL)
	    {
    	  if (TermSymb (tl->term) == var)
	    	  {
	    		  return true;
	    	  }
	      tl = tl->next;
	    }
 	 }
 return false;
}
Term
levelFind (Symbol s, int level)
{
  Termlist tl;

  tl = leveltl[level];
  while (tl != NULL)
    {
      if (isTermLeaf (tl->term))
	{
	  if (TermSymb (tl->term) == s)
	    {
	      return tl->term;
	    }
	}
      tl = tl->next;
    }
  return NULL;
}

Term
symbolFindForPattern (Symbol s)
{
	  int i;
	  Term t;

	  i = MAXLEVELS-1;
	  while (i >= 0)
	    {
	      t = levelFind (s, i);
	      if (t != NULL)
		return t;
	      i--;
	    }
  return NULL;
}


Term
symbolFind (Symbol s)
{
  int i;
  Term t;

  i = level;
  while (i >= 0)
    {
      t = levelFind (s, i);
      if (t != NULL)
	return t;
      i--;
    }
  return NULL;
}

//! Yield a basic global constant term (we suppose it exists) or NULL, given a string
Term
findGlobalConstant (const char *s)
{
  return levelFind (lookup (s), 0);
}

void
defineUsertype (Tac tcdu)
{
  Tac tc;
  Term t;
  Term tfind;

  tc = tcdu->t1.tac;

  if (tc == NULL)
    {
      error ("Empty usertype declaration on line %i.", tcdu->lineno);
    }
  while (tc != NULL && tc->op == TAC_STRING)
    {
      /* check whether this term is already declared in the same way
       * (i.e. as a type) */

      tfind = levelFind (tc->t1.sym, 0);
      if (tfind == NULL)
	{
	  /* this is what we expected: this type is not declared yet */
	  t = levelDeclare (tc->t1.sym, 0, 0);
	  t->stype = termlistAdd (NULL, TERM_Type);
	}
      else
	{
	  /* oi!, there's already one. Let's hope is is a type too. */
	  if (inTermlist (tfind->stype, TERM_Type))
	    {
	      if (switches.check)
		{
		  /* phew. warn anyway */
		  globalError++;
		  eprintf ("warning: double declaration of usertype ");
		  termPrint (tfind);
		  eprintf ("\n");
		  globalError--;
		}
	    }
	  else
	    {
	      /* that's not right! */
	      error
		("Conflicting definitions in usertype definition on line %i.",
		 tc->lineno);
	    }
	}
      tc = tc->next;
    }
}

//! Declare a variable (constant) at the current level
void
levelTacDeclaration (Tac tc, int isVar)
{
  Tac tscan;
  Termlist typetl = NULL;
  Term t;
  int isAgent;

  // tscan contains the type list (as is const x,z: Term or var y: Term,Ding)
  tscan = tc->t2.tac;
  if (!isVar && tscan->next != NULL)
    {
      error ("Multiple type definition for constant on line %i.",
	     tscan->lineno);
    }
  // scan the whole type info list
  while (tscan != NULL && tscan->op == TAC_STRING)
    {
      /* apparently there is type info, termlist? */
      t = levelFind (tscan->t1.sym, 0);

      if (t == NULL)
	{
	  /* not declared, that is unacceptable. */
	  error ("Undeclared type on line %i.", tscan->lineno);
	}
      else
	{
	  if (!inTermlist (t->stype, TERM_Type))
	    {
	      error ("Non-type constant in type declaration on line %i.",
		     tscan->lineno);
	    }
	}
      typetl = termlistAdd (typetl, t);
      tscan = tscan->next;
    }
  /* check whether the type list contains the agent type */
  isAgent = inTermlist (typetl, TERM_Agent);

  /* parse all constants and vars, because a single declaration can contain multiple ones */
  tscan = tc->t1.tac;
  while (tscan != NULL)
    {
      /* declare this variable/constant with the previously derived type list */
      t = symbolDeclare (tscan->t1.sym, isVar);
      t->stype = typetl;
      /* local to the role? */
      if (level == 2)
	{
	  if (isVar)
	    {
	      /* it is a role variable, so add it to the nicely declared variables */
	      thisRole->declaredvars =
		termlistAdd (thisRole->declaredvars, t);
	    }
	  else
	    {
	      /* it is a role constant, so add it to the nicely declared constants */
	      thisRole->declaredconsts =
		termlistAdd (thisRole->declaredconsts, t);
	    }
	}
      else if (level == 0)
	{
	  sys->globalconstants = termlistAdd (sys->globalconstants, t);
	  if (isAgent)
	    {
	      sys->agentnames = termlistAdd (sys->agentnames, t);
	    }
	}
      tscan = tscan->next;
    }
}

//! Get last role def
Roledef
getLastRoledef (Roledef rd)
{
  if (rd != NULL)
    {
      while (rd->next != NULL)
	{
	  rd = rd->next;
	}
    }
  return rd;
}

//! Mark last roledef lineno
void
markLastRoledef (Roledef rd, const int lineno)
{
  rd = getLastRoledef (rd);
  rd->lineno = lineno;
}


//! Check whether a claim label already occurs
int
isClaimlabelUsed (const System sys, const Term label)
{
  Claimlist cl;

  if (label == NULL)
    {
      /* we assign this 'occurs' because it is an invalid label */
      return true;
    }
  cl = sys->claimlist;
  while (cl != NULL)
    {
      if (isTermEqual (cl->label, label))
	{
	  return true;
	}
      cl = cl->next;
    }
  return false;
}

//! Generate a fresh claim label
Term
generateFreshClaimlabel (const System sys, const Protocol protocol,
			 const Role role, const Term claim, const int n)
{
  Term label;

  /* Simply use the role as a prefix */
  label = freshTermPrefix (role->nameterm);
  label = makeTermTuple (protocol->nameterm, label);
  return label;
}

//! Boolean sanity wrapper around C low level madness
int
isStringEqual (const char *s1, const char *s2)
{
  return (strcmp (s1, s2) == 0);
}

//! Check sanity of the parameters occurring in a claim
/**
 * Check if all variables have been received before.
 * If not, aborts with error.
 */
void
checkParameterGround (Claimlist cl)
{
  Termlist claimvars;
  Termlist recvvars;
  Termlist cli;

  /* Compute received variables and those occurring in the claim parameter */
  claimvars = termlistAddVariables (NULL, cl->parameter);
  recvvars = compute_recv_variables (thisRole);

  cli = claimvars;
  while (cli != NULL)
    {
      if (!inTermlist (thisProtocol->rolenames, cli->term))
	{
	  /* only if it is not a role */
	  if (!inTermlist (recvvars, cli->term))
	    {
	      /* this claimvar does not occur in the recvs? */
	      /* abort with error */
	      error_pre ();
	      globalError++;
	      eprintf ("Claim of role ");
	      termPrint (cl->rolename);
	      eprintf (" contains a variable ");
	      termPrint (cli->term);
	      eprintf
		(" which is not initialized before (i.e., not received), on line %i.",
		 cl->lineno);
	      globalError--;
	      error_post ("");
	    }
	}
      cli = cli->next;
    }
  termlistDelete (claimvars);
  termlistDelete (recvvars);
  return;
}

//! Check if claim is of certain type, then check if meets parameter range, if not abort with error
void
checkParameterRange (const Claimlist cl, const Term claimtype, int minargs,
		     int maxargs)
{
  Termlist params;
  int num;

  if (cl->type != claimtype)
    {
      return;
    }

  params = tuple_to_termlist (cl->parameter);
  num = termlistLength (params);

  if (minargs == -1)
    {
      minargs = num - 1;
    }
  if (maxargs == -1)
    {
      maxargs = num + 1;
    }

  if ((num < minargs) || (num > maxargs))
    {
      error_pre ();
      globalError++;
      termPrint (cl->type);
      eprintf (" claim of role ");
      termPrint (cl->rolename);
      eprintf (" on line %i", cl->lineno);
      if (maxargs == 0)
	{
	  error_post (" does not require any arguments.");
	}
      else
	{
	  if (num < minargs)
	    {
	      eprintf (" requires at least");
	    }
	  else
	    {
	      eprintf (" requires at most");
	    }
	  error_post (" %i arguments.", maxargs);
	}
    }
  termlistDelete (params);
}

//! Create a claim and add it to the claims list, and add the role event.
Claimlist
claimCreate (const System sys, const Protocol protocol, const Role role,
	     const Term claim, Term label, const Term msg, const int lineno)
{
  Claimlist cl;
  int len;

  len = roledef_length (role->roledef);

  /* generate full unique label */
  /* is the label empty or used? */
  if (label == NULL || isClaimlabelUsed (sys, label))
    {
      /* simply generate a fresh one */
      label = generateFreshClaimlabel (sys, protocol, role, claim, len);
    }

  // Assert: label is unique, add claimlist info
  cl = malloc (sizeof (struct claimlist));
  cl->type = claim;
  cl->label = label;
  cl->parameter = msg;
  cl->protocol = thisProtocol;
  cl->rolename = role->nameterm;
  cl->role = role;
  cl->roledef = NULL;
  cl->count = 0;
  cl->complete = 0;
  cl->timebound = 0;
  cl->failed = 0;
  cl->states = 0;
  cl->prec = NULL;
  cl->roles = NULL;
  cl->alwaystrue = false;
  cl->warnings = false;
  cl->lineno = lineno;

  /* add the claim to the end of the current list */
  cl->next = NULL;
  if (sys->claimlist == NULL)
    {
      sys->claimlist = cl;
    }
  else
    {
      Claimlist cl2;

      cl2 = sys->claimlist;
      while (cl2->next != NULL)
	{
	  cl2 = cl2->next;
	}
      cl2->next = cl;
    }

  /* add the role event */
  role->roledef = roledefAdd (role->roledef, CLAIM, label,
			      role->nameterm, claim, msg, cl);
  markLastRoledef (role->roledef, lineno);

  /* possible special handlers for each claim */

  if ((claim == CLAIM_Secret) || (claim == CLAIM_SKR))
    {
      Termlist claimvars;
      Termlist recvvars;
      Termlist cli;

      /* now check whether the claim contains variables that can actually be influenced by the intruder */

      claimvars = termlistAddVariables (NULL, cl->parameter);
      recvvars = compute_recv_variables (thisRole);
      cli = claimvars;
      while (cli != NULL)
	{
	  if (!inTermlist (thisProtocol->rolenames, cli->term))
	    {
	      /* only if it is not a role */
	      if (!inTermlist (recvvars, cli->term))
		{
		  /* this claimvar does not occur in the recvs? */
		  /* then we should ignore it later */
		  cl->alwaystrue = true;
		  cl->warnings = true;

		  /* show a warning for this */
		  globalError++;
		  warning_pre ();
		  eprintf ("Secrecy claim of role ");
		  termPrint (cl->rolename);
		  eprintf (" contains a variable ");
		  termPrint (cli->term);
		  eprintf
		    (" which is never received; therefore the claim will be true.\n");
		  globalError--;
		}
	    }
	  cli = cli->next;
	}
      termlistDelete (claimvars);
      termlistDelete (recvvars);
    }
  else
    {
      /* If it is NOT a SECRET claim, then check parameters are ground */
      checkParameterGround (cl);
    }

  if ((claim == CLAIM_Commit) || (claim == CLAIM_Running))
    {
      /* Check that Claim syntax is role,commit,role,data
       */
      Termlist params;

      params = tuple_to_termlist (cl->parameter);

      if (termlistLength (params) < 2)
	{
	  /* yield error */
	  globalError++;
	  warning_pre ();
	  termPrint (claim);
	  eprintf (" claim of role ");
	  termPrint (cl->rolename);
	  eprintf
	    (" requires four arguments. Please specify both the target role and the data to agree on, as in:\n");
	  warning_pre ();
	  eprintf ("  claim(R,  Commit,  R', data )\n");
	  warning_pre ();
	  eprintf ("and\n");
	  warning_pre ();
	  eprintf ("  claim(R', Running, R,  data ).\n");
	  globalError--;
	  error
	    ("Incorrect number of arguments in Commit/Running claim at line %i.",
	     lineno);
	}
      else
	{
	  // The length is at least two, so we can obtain the first element
	  Term targetrole;

	  targetrole = params->term;
	  if (!inTermlist (protocol->rolenames, targetrole))
	    {
	      /* yield error */
	      globalError++;
	      warning_pre ();
	      termPrint (claim);
	      eprintf (" claim of role ");
	      termPrint (cl->rolename);
	      eprintf (" specifies the target role to be '");
	      termPrint (targetrole);
	      eprintf ("', which is not a role name.\n");
	      warning_pre ();
	      eprintf ("Please use:\n");
	      warning_pre ();
	      eprintf ("  claim(R,  Commit,  R', data )\n");
	      warning_pre ();
	      eprintf ("and\n");
	      warning_pre ();
	      eprintf ("  claim(R', Running, R,  data ).\n");
	      globalError--;
	      error
		("Incorrect target role in Commit/Running claim at line %i.",
		 lineno);
	    }
	}
    }
  checkParameterRange (cl, CLAIM_Secret, 1, -1);
  checkParameterRange (cl, CLAIM_SKR, 1, -1);
  checkParameterRange (cl, CLAIM_Alive, 0, 1);
  checkParameterRange (cl, CLAIM_Weakagree, 0, 1);
  checkParameterRange (cl, CLAIM_Nisynch, 0, 0);
  checkParameterRange (cl, CLAIM_Niagree, 0, 0);
  checkParameterRange (cl, CLAIM_Reachable, 0, 0);
  checkParameterRange (cl, CLAIM_SID, 1, -1);

  return cl;
}

//! Parse a match event, and add role definitions for it
/**
 * Implemented as pure syntactic sugar:
 *
 *   match(pattern,term)
 *
 * is essentially replaced by:
 *
 *   fresh XX;
 *   send( {term}XX );
 *   recv( {pattern}XX );
 *
 */
void
matchEvent (Tac tc)
{
  Term myrole;
  Term msg1, msg2;
  Term tvar;
  Term mmsg;
  Term mpat;
  Symbol nsymb;
  Term label1;
  Labelinfo linfo;

  /* Create fresh Nonce variable */
  nsymb = symbolNextFree (TermSymb (TERM_Hidden));
  tvar = symbolDeclare (nsymb, false);
  //tvar->stype = termlistAdd(NULL,TERM_Nonce);

  /* Make the concrete messages */
  mpat = tacTerm (tc->t1.tac);
  mmsg = tacTerm (tc->t2.tac);
  msg1 = makeTermEncrypt (mmsg, tvar);
  msg2 = makeTermEncrypt (mpat, tvar);

  /* Declare the const */
  thisRole->declaredconsts = termlistAdd (thisRole->declaredconsts, tvar);

  /* And send & recv combo (implementing the syntactic sugar) */
  label1 = freshTermPrefix (LABEL_Match);
  linfo = label_create (label1, thisProtocol);
  sys->labellist = list_append (sys->labellist, linfo);
  myrole = thisRole->nameterm;

  /* add send event */
  thisRole->roledef =
    roledefAdd (thisRole->roledef, SEND, label1, myrole, myrole, msg1, NULL);
  markLastRoledef (thisRole->roledef, tc->lineno);
  /* add recv event */
  thisRole->roledef =
    roledefAdd (thisRole->roledef, RECV, label1, myrole, myrole, msg2, NULL);
  markLastRoledef (thisRole->roledef, tc->lineno);
}

//! Parse a non-match event, and add role definitions for it
/**
 * Currently implemented by introducing a special claim.
 *
 * Claim(R,NotEqual,(pat,term) );
 *
 * This special claim, notequal, is later used for pruning.
 */
void
nonMatchEvent (Tac tc)
{
  Term msg;
  Term mpat;
  Term mmsg;

  mpat = tacTerm (tc->t1.tac);
  mmsg = tacTerm (tc->t2.tac);
  msg = makeTermTuple (mpat, mmsg);
  claimCreate (sys, thisProtocol, thisRole, CLAIM_Notequal, NULL, msg,
	       tc->lineno);
}

//! Parse a communication event tc of type event, and add a role definition event for it.
void
commEvent (int event, Tac tc)
{
  /* Add an event to the roledef, send or recv */
  Claimlist cl;
  Term fromrole = NULL;
  Term torole = NULL;
  Term msg = NULL;
  Term label = NULL;
  Term claim = NULL;
  Term claimbig = NULL;
  int n = 0;
  Tac trip;
  Labelinfo linfo;

  /* Construct label, if any */
  if (tc->t1.sym == NULL)
    {
      /* right, now this should not be NULL anyway, if so we construct a fresh one.
       * This can be a weird choice if it is a recv or send, because in that case
       * we cannot chain them anymore and the send-recv correspondence is lost.
       */
      int n;
      Roledef rd;

      n = 1;
      for (rd = thisRole->roledef; rd != NULL; rd = rd->next)
	{
	  if (rd->type == CLAIM)
	    {
	      n++;
	    }
	}
      label = intTermPrefix (n, thisRole->nameterm);
     }
  else
    {
      label = levelFind (tc->t1.sym, level - 1);
    if (label == NULL)
	{
	  /* effectively, labels are bound to the protocol */
	  level--;
	  /* leaves a garbage tuple. dunnoh what to do with it */
	  label = levelConst (tc->t1.sym);
	  level++;
	}
      else
	{
	  /* leaves a garbage tuple. dunnoh what to do with it */
	}
    }
  label = makeTermTuple (thisProtocol->nameterm, label);
  /**
   * Parse the specific event type
   */
  trip = tc->t2.tac;
  switch (event)
    {
    case RECV:
    case SEND:
      /**
       * We know the label. Find the corresponding labelinfo bit or make a new one
       */
      linfo = label_find (sys->labellist, label);
      if (linfo == NULL)
	{
	  /* Not found, make a new one */
	  linfo = label_create (label, thisProtocol);
	  sys->labellist = list_append (sys->labellist, linfo);
	}

      /* now parse triplet info */
      if (trip == NULL || trip->next == NULL || trip->next->next == NULL)
	{
	  error ("Problem with %i event on line %i.", event, tc->lineno);
	}
      fromrole = tacTerm (trip);
      torole = tacTerm (trip->next);
      msg = tacTerm (tacTuple ((trip->next->next)));
      cl = NULL;

      if (event == SEND)
	{
	  /* set sendrole */
	  if (!isTermEqual (fromrole, thisRole->nameterm))
	    error
	      ("Send role does not correspond to execution role at line %i.",
	       tc->lineno);
	  if (linfo->sendrole != NULL)
	    error ("Label defined twice for sendrole!");
	  linfo->sendrole = fromrole;

	  /* set keylevels based on send events */
	  term_set_keylevels (fromrole);
	  term_set_keylevels (torole);
	  term_set_keylevels (msg);
	}
      else
	{
	  // RECV
	  /* set recvrole */
	  if (!isTermEqual (torole, thisRole->nameterm))
	    error
	      ("Recv role does not correspond to execution role at line %i.",
	       tc->lineno);
	  if (linfo->recvrole != NULL)
	    error ("Label defined twice for recvrole!");
	  linfo->recvrole = torole;
	}

      /* and make that recv/send event */
      thisRole->roledef = roledefAdd (thisRole->roledef, event, label,
				      fromrole, torole, msg, cl);
      /* mark last one with line number */
      markLastRoledef (thisRole->roledef, tc->lineno);
      break;

    case CLAIM:
      /* switch can be used to remove all *parsed* claims */
      if (!switches.removeclaims)
	{
	  /* now parse tuple info */
	  if (trip == NULL || trip->next == NULL)
	    {
	      error ("Problem with claim %i event on line %i.", event,
		     tc->lineno);
	    }
	  fromrole = tacTerm (trip);
	  claimbig = tacTerm (tacTuple ((trip->next)));
	  /* check for several types */
	  claim = tupleProject (claimbig, 0);
	  torole = claim;

	  /* check for obvious flaws */
	  if (claim == NULL)
	    {
	      error ("Invalid claim specification on line %i.", tc->lineno);
	    }
	  if (!inTermlist (claim->stype, TERM_Claim))
	    {
	      globalError++;
	      eprintf ("error: [%i] claim term is not of claim type ",
		       trip->next->lineno);
	      termPrint (claim);
	      errorTac (trip->next->lineno);
	      globalError--;
	    }
	  /* unfold parameters to msg */
	  msg = NULL;
	  n = tupleCount (claimbig) - 1;
	  if (n < 1)
	    {
	      /* no parameters */
	      n = 0;
	    }
	  else
	    {
	      /* n parameters */
	      msg = TermOp2 (deVar (claimbig));
	      if (tupleCount (msg) != n)
		{
		  error ("Problem with claim tuple unfolding at line %i.",
			 trip->next->lineno);
		}
	    }

	  // check whether label is unique

	  if (isClaimlabelUsed (sys, label))
	    {
	      if (switches.check)
		{
		  warning
		    ("Claim label is not unique at line %i, generating fresh label.",
		     tc->lineno);
		}
	      // the reported new label will be generated later in claimCreate()
	    }

	  if (!isTermEqual (fromrole, thisRole->nameterm))
	    error
	      ("Claim role does not correspond to execution role at line %i.",
	       tc->lineno);

	  /* handles claim types with different syntactic claims */

	  if ((claim == CLAIM_Secret) || (claim == CLAIM_SKR))
	    {
	      if (n == 0)
		{
		  error
		    ("Secrecy claim requires a list of terms to be secret on line %i.",
		     trip->next->lineno);
		}
	      if (n > 1)
		{
		  error
		    ("Secrecy claim on line %i should not contain tuples (for Arachne) until it is officially supported.",
		     trip->next->lineno);
		}
	    }
	  if (claim == CLAIM_Nisynch)
	    {
	      if (n != 0)
		{
		  error ("NISYNCH claim requires no parameters at line %i.",
			 trip->next->lineno);
		}
	    }
	  if (claim == CLAIM_Niagree)
	    {
	      if (n != 0)
		{
		  error ("NIAGREE claim requires no parameters at line %i.",
			 trip->next->lineno);
		}
	    }

	  /* create the event */

	  cl =
	    claimCreate (sys, thisProtocol, thisRole, claim, label, msg,
			 tc->lineno);
	}
      break;
    }
}

//! Create hash functions
/**
 * Assumption: hfuncs list in same order as tac.
 *
 * Note: Destroys tc contents, so please don't reuse afterwards.
 */
int
hashfunctions (Tac tcstart)
{
  Termlist hfuncs;
  Termlist hinvs;
  Tac tc;

  // As long as tc is intact.
  levelDeclareConst (tcstart);
  hfuncs = tacTermlist (tcstart->t1.tac);
  if (level < 2)
    knowledgeAddTermlist (sys->know, hfuncs);

  for (tc = tcstart->t1.tac; tc != NULL; tc = tc->next)
    {
      tc->t1.sym = symbolNextFree (symbolSysConst ("_unhash-"));
    }
  levelDeclareConst (tcstart);
  hinvs = tacTermlist (tcstart->t1.tac);

  while (hfuncs != NULL)
    {
      if (hinvs == NULL)
	{
	  error
	    ("Bug in hashfunction generation code. Please contact the authors.\n");
	}
      knowledgeAddInverseKeys (sys->know, hfuncs->term, hinvs->term);
      hfuncs->term->stype = termlistAdd (NULL, TERM_Function);
      if (tcstart->t3.tac == NULL)
	{
	  // Not secret
	  knowledgeAddTerm (sys->know, hfuncs->term);
	  knowledgeAddPublicFunction (sys->know, hfuncs->term);
	}
      hinvs->term->stype = termlistAdd (NULL, TERM_Function);
      hfuncs = hfuncs->next;
      hinvs = hinvs->next;
    }
  return true;
}


int
normalDeclaration (Tac tc)
{
  switch (tc->op)
    {
    case TAC_VAR:
      levelDeclareVar (tc);
      if (level < 2 && tc->t3.tac == NULL)
	knowledgeAddTermlist (sys->know, tacTermlist (tc->t1.tac));
      break;
    case TAC_CONST:
      levelDeclareConst (tc);
      if (level < 2 && tc->t3.tac == NULL)
	knowledgeAddTermlist (sys->know, tacTermlist (tc->t1.tac));
      if (level > 0)
	{
	  globalError++;
	  warning_pre ();
	  eprintf ("const ");
	  termlistPrint (tacTermlist (tc->t1.tac));
	  eprintf
	    (" usage inside roles is deprecated. Please use 'fresh' instead on line %i.\n",
	     tc->lineno);
	  globalError--;
	}
      break;
    case TAC_FRESH:
      levelDeclareConst (tc);
      if (level < 2)
	{
	  globalError++;
	  error_pre ();
	  eprintf ("fresh terms ");
	  termlistPrint (tacTermlist (tc->t1.tac));
	  eprintf (" should be declared inside roles,");
	  errorTac (tc->lineno);	// exits Scyther here
	  globalError--;
	}
      break;
    case TAC_SECRET:
      levelDeclareConst (tc);
      break;
    case TAC_COMPROMISED:
      knowledgeAddTermlist (sys->know, tacTermlist (tc->t1.tac));
      break;
    case TAC_INVERSEKEYS:
      knowledgeAddInverseKeys (sys->know, tacTerm (tc->t1.tac),
			       tacTerm (tc->t2.tac));
      break;
    case TAC_INVERSEKEYFUNCTIONS:
      knowledgeAddInverseKeyFunctions (sys->know, tacTerm (tc->t1.tac),
				       tacTerm (tc->t2.tac));
      break;
    case TAC_HASHFUNCTION:
      hashfunctions (tc);
      break;
    default:
      /* abort with false */
      return 0;
    }
  return 1;
}

//! Add all sorts of claims to this role
void
claimAddAll (const System sys, const Protocol protocol, const Role role)
{
  /* first: secrecy claims for all locally declared things */
  void addSecrecyList (Termlist tl)
  {
    while (tl != NULL)
      {
	Term t;

	t = deVar (tl->term);
	if (realTermLeaf (t))
	  {
	    // Add a secrecy claim
	    claimCreate (sys, protocol, role, CLAIM_Secret, NULL, t, -1);
	  }
	tl = tl->next;
      }
  }

  if (!isHelperProtocol (protocol))
    {
      addSecrecyList (role->declaredconsts);
      addSecrecyList (role->declaredvars);

      /* full non-injective agreement and ni-synch */
      claimCreate (sys, protocol, role, CLAIM_Alive, NULL, NULL, -1);
      claimCreate (sys, protocol, role, CLAIM_Weakagree, NULL, NULL, -1);
      claimCreate (sys, protocol, role, CLAIM_Niagree, NULL, NULL, -1);
      claimCreate (sys, protocol, role, CLAIM_Nisynch, NULL, NULL, -1);
    }
}

//! Compile a role
/**
 * Input: a name and a roledef tac
 *
 * Upon return, thisRole should contain the role definition
 */
void
roleCompile (Term nameterm, Tac tc)
{
  /* locate the role, protocol into thisRole */
  /* scan through role list */
  thisRole = thisProtocol->roles;
  while (thisRole != NULL && !isTermEqual (thisRole->nameterm, nameterm))
    {
      thisRole = thisRole->next;
    }
  if (thisRole == NULL)
    {
      globalError++;
      eprintf ("error: [%i] undeclared role name ", tc->lineno);
      termPrint (nameterm);
      eprintf (" in line ");
      errorTac (tc->lineno);
    }

  /* parse the content of the role */
  levelInit ();

  {
    int firstEvent;

    /* initiator/responder flag not set */
    firstEvent = 1;

    while (tc != NULL)
      {
	switch (tc->op)
	  {
	  case TAC_RECV:
	    if (firstEvent)
	      {
		// First a recv, thus responder
		/*
		 * Semantics: defaults (in role.c) to initiator _unless_ the first event is a recv,
		 * in which case we assume that the agent names are possibly received as variables
		 */
		thisRole->initiator = 0;
		firstEvent = 0;
	      }
	    commEvent (RECV, tc);
	    break;
	  case TAC_SEND:
	    firstEvent = 0;
	    commEvent (SEND, tc);
	    break;
	  case TAC_MATCH:
	    if (tc->t3.value == true)
	      {
		matchEvent (tc);
	      }
	    else
	      {
		nonMatchEvent (tc);
	      }
	    break;
	  case TAC_CLAIM:
	    commEvent (CLAIM, tc);
	    break;
	  case TAC_KNOWS:
	    roleKnows (tc);
	    break;
	  default: //parse declaration (variables, fresh values, constants)
	    if (!normalDeclaration (tc))
	      {
		globalError++;
		eprintf ("error: [%i] illegal command %i in role ",
			 tc->lineno, tc->op);
		termPrint (thisRole->nameterm);
		eprintf (" ");
		errorTac (tc->lineno);
	      }
	    break;
	  }
	tc = tc->next;
      }
  }

  /* add any claims according to the switches */

  if (switches.addreachableclaim)
    {
      if (!isHelperProtocol (thisProtocol))
	{
	  claimCreate (sys, thisProtocol, thisRole, CLAIM_Reachable, NULL,
		       NULL, -1);
	}
    }
  if (switches.addallclaims)
    {
      claimAddAll (sys, thisProtocol, thisRole);
    }

  /* last bits */
  compute_role_variables (sys, thisProtocol, thisRole);
  levelDone ();
}

//! Initial role knowledge declaration
void
roleKnows (Tac tc)
{
  sys->knowledgedefined = true;	// apparently someone uses this, so we enable the check
  thisRole->knows =
    termlistConcat (thisRole->knows, tacTermlist (tc->t1.tac));
}

void
runInstanceCreate (Tac tc)
{
  /* create an instance of an existing role
   * tac1 is the dot-separated reference to the role.
   * tac2 is the list of parameters to be filled in.
   */

  Protocol p;
  Role r;
  Symbol psym, rsym;
  Termlist instParams;

  /* check whether we can still do it */
  if (sys->maxruns >= maxruns)
    return;

  /* first, locate the protocol */
  psym = tc->t1.tac->t1.sym;
  p = sys->protocols;
  while (p != NULL && TermSymb (p->nameterm) != psym)
    p = p->next;
  if (p == NULL)
    {
      globalError++;
      eprintf
	("error: [%i] Trying to create a run of a non-declared protocol ",
	 tc->lineno);
      symbolPrint (psym);
      eprintf (" ");
      errorTac (tc->lineno);
    }

  /* locate the role */
  rsym = tc->t1.tac->t2.sym;
  r = p->roles;
  while (r != NULL && TermSymb (r->nameterm) != rsym)
    r = r->next;
  if (r == NULL)
    {
      globalError++;
      eprintf ("error: [%i] Protocol ", tc->lineno);
      symbolPrint (psym);
      eprintf (" has no role called ");
      symbolPrint (rsym);
      eprintf (" ");
      errorTac (tc->lineno);
    }

  /* we now know what we are instancing, equal numbers? */
  instParams = tacTermlist (tc->t2.tac);
  if (termlistLength (instParams) != termlistLength (p->rolenames))
    {
      globalError++;
      eprintf
	("error: [%i] Run instance has different number of parameters than protocol ",
	 tc->lineno);
      termPrint (p->nameterm);
      eprintf (" ");
      errorTac (tc->lineno);
    }

  /* equal numbers, so it seems to be safe */
  roleInstance (sys, p, r, instParams, NULL);	// technically, we don't need to do this for Arachne [fix later]

  /* after creation analysis */
  /* originator assumption for CLP ? */
  /* TODO */
}

//! Check whether the roles in a protocol are non-empty
void
checkProtocolRoles (void)
{
  Role role;
  Termlist badroles;

  badroles = NULL;
  role = thisProtocol->roles;
  while (role != NULL)
    {
      if (role->roledef == NULL)
	{
	  // Hey, this role is empty.
	  badroles = termlistAdd (badroles, role->nameterm);
	}
      role = role->next;
    }

  if (badroles != NULL)
    {
      globalError++;
      eprintf ("warning: protocol ");
      termPrint (thisProtocol->nameterm);
      eprintf (" has empty role definitions for the roles: ");
      termlistPrint (badroles);
      eprintf ("\n");
      globalError--;
      termlistDelete (badroles);
    }
}

//! Compile a protocol description
void
protocolCompile (Symbol prots, Tac tc, Tac tcroles)
{
  Protocol pr;
  Term t;

  /* make new (empty) current protocol with name */
  pr = protocolCreate (levelConst (prots));
  thisProtocol = pr;
  {
    // check for double name declarations
    Protocol prold;

    prold = sys->protocols;
    while (prold != NULL)
      {
	if (isTermEqual (pr->nameterm, prold->nameterm))
	  {
	    globalError++;
	    eprintf ("error: [%i] Double declaration of protocol ",
		     tc->lineno);
	    symbolPrint (prots);
	    eprintf (" ");
	    errorTac (tc->lineno);
	  }
	prold = prold->next;
      }
  }

  /* add protocol to list */
  pr->next = sys->protocols;
  sys->protocols = pr;
  protocolCount++;

  levelInit ();
  /* add the role names */
  pr->rolenames = NULL;
  while (tcroles != NULL)
    {
      Term rolename;
      Role r;

      rolename = levelVar (tcroles->t1.sym);
      rolename->stype = termlistAdd (NULL, TERM_Agent);

      /* add name to list of role names */
      pr->rolenames = termlistAppend (pr->rolenames, rolename);
      /* make new (empty) current protocol with name */
      r = roleCreate (rolename);
      /* add role to role list of the protocol */
      r->next = thisProtocol->roles;
      thisProtocol->roles = r;
      /* next role name */
      tcroles = tcroles->next;
    }

  /* parse the content of the protocol */
  while (tc != NULL)
    {
      switch (tc->op)
	{
	case TAC_UNTRUSTED:
	  sys->untrusted =
	    termlistConcat (sys->untrusted, tacTermlist (tc->t1.tac));
	  break;
	case TAC_ROLE:
	  t = levelFind (tc->t1.sym, level);
	  if (t != NULL)
	    {
	      // Compile a role
	      roleCompile (t, tc->t2.tac);
	      // singular?
	      if (tc->t3.value != 0)
		{
		  thisRole->singular = true;
		}
	    }
	  else
	    {
	      globalError++;
	      eprintf ("warning: undeclared role name");
	      symbolPrint (tc->t1.sym);
	      eprintf (" in protocol ");
	      termPrint (pr->nameterm);
	      globalError--;
	    }
	  break;
	default:
	  if (!normalDeclaration (tc))
	    {
	      globalError++;
	      eprintf ("error: [%i] illegal command %i in protocol ",
		       tc->lineno, tc->op);
	      termPrint (thisProtocol->nameterm);
	      errorTac (tc->lineno);
	    }
	  break;
	}
      tc = tc->next;
    }

  /* new we should have parsed each protocol role. check this. */
  checkProtocolRoles ();

  levelDone ();
}
/*
Termlist defineUserSubtype(Tac stype, Termlist tl){
	Tac tc = stype->t1.tac;
	Term type1, type2;
	if(tc==NULL)
    {
      error ("Empty subtype declaration on line %i.", tc->lineno);
    }
  while (tc != NULL)
    {
      type1 = levelFind (tc->t1.sym, 0);
      type2 = levelFind(tc->t2.sym,0);
      if (type1 == NULL)
          error ("Type %s is undeclared before being used on line %i.", tc->t1.sym->text, tc->lineno);
      else if(type2==NULL)
          error ("Type %s is undeclared before being used on line %i.", tc->t2.sym->text, tc->lineno);
      else //both types are declared
      {
   		  //then type1 is a subtype of type2
   		  if(!inTermlist(tl,type1))
   			  tl=termlistAdd(tl,type1);
   		  type1->stype = termlistAppend(type1->stype, type2);
      }
      tc = tc->next;
    }
	return tl;
}
void computeSubtypingClosureForTerm(Term type){
	if(type->isSubtypeComputed=='y')
		error("Subtyping is cyclic");
	type->isSubtypeComputed='y';
	Termlist temptl = ((Termlist)type->stype)->next;//ignore the first element in the list as it is not userdefine type
	//if there is only one type then nothing to compute, we mark by 'y'
	if(temptl==NULL)
		type->subtypeClosure='y';
	//otherwise, we iterate over all super-types
	else
	{
		while(temptl!=NULL){
		Term supertype = temptl->term;
		if(supertype->subtypeClosure!='y')
		   computeSubtypingClosureForTerm(supertype);
		type->stype = termlistCheckandAppend((Termlist)type->stype, (Termlist)supertype->stype);
		temptl=temptl->next;
	   }
		type->subtypeClosure='y';
	}
	return;
}

void computeSubtypingClosureForList(Termlist tl){
	while(tl!=NULL){
		computeSubtypingClosureForTerm(tl->term);
		//printf("Type %s has super type:", tl->term->left.symb->text);
		Termlist st = tl->term->stype;
		while(st!=NULL)st=st->next;
		tl=tl->next;
	}
}
*/

void typingDeclare(Tac t){
	Term type = tacTerm(t->t2.tac);
	Tac varlist = t->t1.tac;
	while(varlist!=NULL){
		Term var = levelDeclare(varlist->t1.sym,VARIABLE,MAXLEVELS-1);
		var->stype=NULL;
		var->stype = termlistAdd(var->stype,type); //override if it is already declared
		varlist = varlist->next;
	}
}

void compileEnvironment(Tac t){
	while(t!=NULL){
		typingDeclare(t);
		t = t->next;
	}
}

//version of tacTerm for pattern variables
Term
tacTermForPattern (Tac tc, int isLeft, int index)
{
  Term t;

  switch (tc->op)
    {
    case TAC_ABSTRACT:
    	t = tacTermForPattern(tc->t1.tac, isLeft,index);
    	if(!isLeft) t->abst = 1;
    	return t;
    case TAC_FCALL:
      t = makeTermEncrypt (tacTermForPattern (tc->t1.tac, isLeft,index),
    		               tacTermForPattern (tc->t2.tac,isLeft,index));
      t->helper.fcall = true;
      return t;
    case TAC_ENCRYPT:
      return makeTermEncrypt (tacTermForPattern (tc->t1.tac, isLeft,index),
    		                  tacTermForPattern (tc->t2.tac, isLeft,index));
    case TAC_TUPLE:
      return makeTermTuple (tacTermForPattern (tc->t1.tac, isLeft,index),
    		                tacTermForPattern (tc->t2.tac, isLeft,index));
    case TAC_STRING:
      {
    	 if(clauseVarFind(tc->t1.sym, index))
    		 	 {
    	    		 globalError++;
    	    		 eprintf ("error: [%i] the variable ", tc->lineno);
    	    		 symbolPrint (tc->t1.sym);
    	    		 eprintf(" has been used in the previous clause");
    	    		 errorTac (tc->lineno);
    		 	 }
    	 Term t = symbolFindForPattern (tc->t1.sym);
    	 if (t == NULL)
    	 {
    		 globalError++;
    		 eprintf ("error: [%i] undeclared variable ", tc->lineno);
    		 symbolPrint (tc->t1.sym);
    		 errorTac (tc->lineno);
    	 }
    	 else if(t->type==VARIABLE){
    		 if(isLeft&&inTermlist(clauseVar[index],t))
    			 error("the patten in line %d is not linear (each variable occurs exactly once",tc->lineno);
    		 clauseVar[index] = termlistAdd(clauseVar[index],t);
    	 }
    	 return t;
      }
    default:
      return NULL;
    }
}

void equationDeclare(Tac t, int index){
	Term left = tacTermForPattern(t->t1.tac, 1, index);
	Term right = tacTermForPattern(t->t2.tac, 0, index);
	if(!checkWelldefinednessForEquation(left,right)){
		error("The equation is not well-defined at line %d",t->lineno);
	}
	Equation eq = makeEquation();
	if(t->op==TAC_PERSISTENT_EQUATION)
	{
		eq->type=USER_DEFINED_PERSISTENT;
		if(isTermEqual(right,TERM_NIL))
			nilfree=2;
	}
	else
	{
		eq->type=USER_DEFINED_LINEAR;
		if(isTermEqual(right,TERM_NIL))
			nilfree=1;
	}
	eq->left = left;
	eq->right=right;
	eq->line=t->lineno;
	eql = equationlistAdd(eql, eq);
}

void compileEquations(Tac t){
	int index = 0;
	while(t!=NULL){
		equationDeclare(t,index);
		t = t->next;
		index++;
	}
	free(clauseVar);
}


void
tacProcess (Tac tc)
{
//	  Termlist newtl=NULL;
  while (tc != NULL)
    {
      switch (tc->op)
	{
	case TAC_PROTOCOL:
	  protocolCompile (tc->t1.sym, tc->t2.tac, tc->t3.tac);
	  break;
	case TAC_UNTRUSTED:
	  sys->untrusted =
	    termlistConcat (sys->untrusted, tacTermlist (tc->t1.tac));
	  break;
	case TAC_RUN:
	  runInstanceCreate (tc);
	  break;
	case TAC_USERTYPE:
	  defineUsertype (tc);
	  break;
	//case TAC_USER_SUBTYPE:
	//	newtl=defineUserSubtype(tc, newtl);
	//  break;
	case TAC_ENV:
		compileEnvironment(tc->t1.tac);
		break;
	case TAC_EQUATIONS:
		compileEquations(tc->t1.tac);
		break;

	default:
	  if (!normalDeclaration (tc))
	    {
	      globalError++;
	      eprintf ("error: [%i] illegal command %i at the global level ",
		       tc->lineno, tc->op);
	      errorTac (tc->lineno);
	    }
	  break;
	}
      tc = tc->next;
    }
}



Term
tacTerm (Tac tc)
{
  Term t;

  switch (tc->op)
    {
    case TAC_FCALL:
      t = makeTermEncrypt (tacTerm (tc->t1.tac), tacTerm (tc->t2.tac));
      t->helper.fcall = true;
      return t;
    case TAC_ENCRYPT:
      return makeTermEncrypt (tacTerm (tc->t1.tac), tacTerm (tc->t2.tac));
    case TAC_TUPLE:
      return makeTermTuple (tacTerm (tc->t1.tac), tacTerm (tc->t2.tac));
    case TAC_STRING:
      {
	Term t ;
	//we check whether a variable used by the protocol has been used before by the abstraction
	//if it is the case, we announce an error.
	if(levelFind(tc->t1.sym,MAXLEVELS-1)){
	    globalError++;
	    eprintf ("error: [%i] the variable %s should not occur in the environment",
	    		tc->lineno, tc->t1.sym->text);
	    errorTac (tc->lineno);
	}
	t= symbolFind (tc->t1.sym);
	if (t == NULL)
	  {
	    globalError++;
	    eprintf ("error: [%i] undeclared symbol ", tc->lineno);
	    symbolPrint (tc->t1.sym);
	    errorTac (tc->lineno);
	  }
	return t;
      }
    default:
      return NULL;
    }
}

//! Extract termlist from tac
/**
 * Note: termlist in same order as tac. This is required for correct working of functions such as 'hashfunctions'.
 */
Termlist
tacTermlist (Tac tc)
{
  Termlist tl = NULL;

  while (tc != NULL)
    {
      tl = termlistAppend (tl, tacTerm (tc));
      tc = tc->next;
    }
  return tl;
}

//! Compute variables for a roles (for Arachne)
/**
 * This also takes care of setting the hasUntypedVariable flag, if needed.
 */
void
compute_role_variables (const System sys, Protocol p, Role r)
{
  if (r->variables == NULL)
    {
      // Not computed before, for some reason
      Termlist tl;

      int process_event (Roledef rd)
      {
	tl = termlistAddVariables (tl, rd->from);
	tl = termlistAddVariables (tl, rd->to);
	tl = termlistAddVariables (tl, rd->message);
	return 1;
      }

      tl = NULL;
      roledef_iterate_events (r->roledef, process_event);
      r->variables = tl;

      /*
       * Iterate over variables for type checks
       */
      for (tl = r->variables; tl != NULL; tl = tl->next)
	{
	  if (isOpenVariable (tl->term))
	    {
	      sys->hasUntypedVariable = true;
	      break;
	    }
	}

#ifdef DEBUG
      if (DEBUGL (5))
	{
	  eprintf ("All variables for role ");
	  termPrint (r->nameterm);
	  eprintf (" are ");
	  termlistPrint (r->variables);
	  eprintf ("\n");
	}
#endif
    }
}

//! Compute term list of rolenames involved in a given term list of labels
Termlist
compute_label_roles (Termlist labels)
{
  Termlist roles;

  roles = NULL;
  while (labels != NULL)
    {
      Labelinfo linfo;

      linfo = label_find (sys->labellist, labels->term);
#ifdef DEBUG
      if (linfo == NULL)
	error ("Label in prec list not found in label info list");
#endif
      roles = termlistAddNew (roles, linfo->sendrole);
      roles = termlistAddNew (roles, linfo->recvrole);

      labels = labels->next;
    }
  return roles;
}

//! Order the label roles for a given claim
void
order_label_roles (const Claimlist cl)
{
  Termlist roles_remaining;
  Termlist roles_ordered;
  int distance;

#ifdef DEBUG
  if (DEBUGL (4))
    {
      eprintf ("Ordering label roles for claim ");
      termPrint (cl->label);
      eprintf ("; 0: ");
      termPrint (cl->rolename);
    }
#endif
  roles_remaining = termlistShallow (cl->roles);
  roles_ordered = termlistAdd (NULL, cl->rolename);
  roles_remaining =
    termlistDelTerm (termlistFind (roles_remaining, cl->rolename));

  distance = 0;
  while (roles_remaining != NULL)
    {
      int scan_label (void *data)
      {
	Labelinfo linfo;
	Termlist tl;

	linfo = (Labelinfo) data;
	if (linfo == NULL)
	  return 1;
	tl = cl->prec;
	if (inTermlist (tl, linfo->label))
	  {
	    if (linfo->protocol == cl->protocol)
	      {
		// If it's not the same protocol, the labels can't match

		// This function checks whether the newrole can connect to the connectedrole, and whether they fulfil their requirements.
		void roles_test (const Term connectedrole, const Term newrole)
		{
		  if (inTermlist (roles_ordered, connectedrole) &&
		      inTermlist (roles_remaining, newrole))
		    {
#ifdef DEBUG
		      if (DEBUGL (4))
			{
			  eprintf (" ");
			  termPrint (newrole);
			}
#endif
		      roles_ordered = termlistAppend (roles_ordered, newrole);
		      roles_remaining =
			termlistDelTerm (termlistFind
					 (roles_remaining, newrole));
		    }
		}

		roles_test (linfo->sendrole, linfo->recvrole);
		roles_test (linfo->recvrole, linfo->sendrole);
	      }
	  }
	return 1;
      }

      distance++;
#ifdef DEBUG
      if (DEBUGL (4))
	{
	  eprintf (" %i:", distance);
	}
#endif
      list_iterate (sys->labellist, scan_label);
    }
  cl->roles = roles_ordered;
#ifdef DEBUG
  if (DEBUGL (4))
    {
      eprintf ("\n");
    }
#endif
}

//! Compute prec() sets for each claim.
/**
 * Generates two auxiliary structures. First, a table that contains
 * a mapping from all events to event/claim labels.
 * A second table is used to compute the precedence order, and 
 * Warshall's algorithm is used to compute the transitive closure.
 * Then, for each claim, the in the preceding labels occurring roles are stored,
 * which is useful later.
 *@returns For each claim in the claim list, a preceding label set is defined.
 */
void
compute_prec_sets (const System sys)
{
  Term *eventlabels;		// array: maps events to labels
  unsigned int *prec;		// array: maps event*event to precedence
  int size;			// temp constant: rolecount * roleeventmax
  int rowsize;
  int r1, r2, ev1, ev2;		// some counters
  Claimlist cl;

  // Assist: compute index from role, lev
  int index (int r, int lev)
  {
    return r * sys->roleeventmax + lev;
  }

  // Assist: yield roledef from r, lev
  Roledef roledef_re (int r, int lev)
  {
    Protocol pr;
    Role ro;
    Roledef rd;

    pr = sys->protocols;
    ro = pr->roles;
    while (r > 0 && ro != NULL)
      {
	ro = ro->next;
	if (ro == NULL)
	  {
	    pr = pr->next;
	    if (pr != NULL)
	      {
		ro = pr->roles;
	      }
	    else
	      {
		ro = NULL;
	      }
	  }
	r--;
      }
    if (ro != NULL)
      {
	rd = ro->roledef;
	while (lev > 0 && rd != NULL)
	  {
	    rd = rd->next;
	    lev--;
	  }
	return rd;
      }
    else
      {
	return NULL;
      }
  }

  // Assist: print matrix
  void show_matrix (void)
  {
    int r1, r2, ev1, ev2;

    r1 = 0;
    while (r1 < sys->rolecount)
      {
	ev1 = 0;
	while (ev1 < sys->roleeventmax)
	  {
	    eprintf ("prec %i,%i:  ", r1, ev1);
	    r2 = 0;
	    while (r2 < sys->rolecount)
	      {
		ev2 = 0;
		while (ev2 < sys->roleeventmax)
		  {
		    eprintf ("%i ",
			     BIT (prec + rowsize * index (r2, ev2),
				  index (r1, ev1)));
		    ev2++;
		  }
		eprintf (" ");
		r2++;
	      }
	    eprintf ("\n");
	    ev1++;
	  }
	eprintf ("\n");
	r1++;
      }
    eprintf ("\n");
  }

  /*
   * Phase 1: Allocate structures and map to labels
   */
  //eprintf ("Rolecount: %i\n", sys->rolecount);
  //eprintf ("Maxevent : %i\n", sys->roleeventmax);
  size = sys->rolecount * sys->roleeventmax;
  rowsize = WORDSIZE (size);
  eventlabels = malloc (size * sizeof (Term));
  prec = (unsigned int *) CALLOC (1, rowsize * size * sizeof (unsigned int));
  // Assign labels
  r1 = 0;
  while (r1 < sys->rolecount)
    {
      Roledef rd;

      ev1 = 0;
      rd = roledef_re (r1, ev1);
      while (rd != NULL)
	{
	  eventlabels[index (r1, ev1)] = rd->label;
	  //termPrint (rd->label);
	  //eprintf ("\t");
	  ev1++;
	  rd = rd->next;
	}
      while (ev1 < sys->roleeventmax)
	{
	  eventlabels[index (r1, ev1)] = NULL;
	  ev1++;
	}
      //eprintf ("\n");
      r1++;
    }
  // Set simple precedence (progress within a role)
  r1 = 0;
  while (r1 < sys->rolecount)
    {
      ev1 = 1;
      while (ev1 < (sys->roleeventmax))
	{
	  SETBIT (prec + rowsize * index (r1, ev1 - 1), index (r1, ev1));
	  ev1++;
	}
      r1++;
    }
  // Scan for label correspondence
  r1 = 0;
  while (r1 < sys->rolecount)
    {
      ev1 = 0;
      while (ev1 < sys->roleeventmax)
	{
	  Roledef rd1;

	  rd1 = roledef_re (r1, ev1);
	  if (rd1 != NULL && rd1->type == SEND)
	    {
	      r2 = 0;
	      while (r2 < sys->rolecount)
		{
		  ev2 = 0;
		  while (ev2 < sys->roleeventmax)
		    {
		      Roledef rd2;

		      rd2 = roledef_re (r2, ev2);
		      if (rd2 != NULL && rd2->type == RECV
			  && isTermEqual (rd1->label, rd2->label))
			{
			  SETBIT (prec + rowsize * index (r1, ev1),
				  index (r2, ev2));
			}
		      ev2++;
		    }
		  r2++;
		}
	    }
	  ev1++;
	}
      r1++;
    }

#ifdef DEBUG
  if (DEBUGL (5))
    {
      show_matrix ();
    }
#endif

  /*
   * Compute transitive closure (Warshall).
   */
  transitive_closure (prec, size);

#ifdef DEBUG
  if (DEBUGL (5))
    {
      show_matrix ();
    }
#endif

  /*
   * Last phase: Process all individual claims
   */
  cl = sys->claimlist;
  while (cl != NULL)
    {
      Roledef rd;
      Term label;
      int claim_index;

      label = cl->label;
      // Locate r,lev from label, requires (TODO) unique labeling of claims!
      r1 = 0;
      ev1 = -1;
      do
	{
	  ev1++;
	  if (ev1 == sys->roleeventmax)
	    {
	      ev1 = 0;
	      r1++;
	    }
	}
      while (r1 < sys->rolecount
	     && !isTermEqual (label, eventlabels[index (r1, ev1)]));

      if (r1 == sys->rolecount)
	{
	  error
	    ("Prec() setup: Could not find the event corresponding to a claim label.");
	}
      rd = roledef_re (r1, ev1);
      if (rd->type != CLAIM)
	{
	  error
	    ("Prec() setup: First event with claim label doesn't seem to be a claim.");
	}
      // Store in claimlist structure
      cl->r = r1;
      cl->ev = ev1;
      cl->roledef = rd;

      /*
       * We have found the claim roledef, and r1,ev1
       * Now we compute the preceding label set
       */
      cl->prec = NULL;		// clear first
      claim_index = index (r1, ev1);
      r2 = 0;
      while (r2 < sys->rolecount)
	{
	  ev2 = 0;
	  rd = roledef_re (r2, ev2);
	  while (rd != NULL)
	    {
	      if (BIT (prec + rowsize * index (r2, ev2), claim_index))
		{
		  // This event precedes the claim

		  if (rd->type == RECV)
		    {
		      // Only store recv labels (but send would work as well)
		      cl->prec = termlistAdd (cl->prec, rd->label);
		    }
		}
	      rd = rd->next;
	      ev2++;
	    }
	  r2++;
	}

      /**
       * ----------------------------------------
       * cl->prec is done, now we infer cl->roles
       * Next, we nicely order them
       * ----------------------------------------
       */

      cl->roles = compute_label_roles (cl->prec);
      order_label_roles (cl);

      /**
       * ---------------------------
       * Distinguish types of claims
       * ---------------------------
       */

      // For ni-synch, the preceding label sets are added to the synchronising_labels sets.
      if (cl->type == CLAIM_Nisynch)
	{
	  Termlist tl_scan;

	  tl_scan = cl->prec;
	  while (tl_scan != NULL)
	    {
	      sys->synchronising_labels =
		termlistAddNew (sys->synchronising_labels, tl_scan->term);
	      tl_scan = tl_scan->next;
	    }
	}

      // For ni-agree, the preceding set is also important, but we furthermore need a restricted
      // synchronising_labels set

      //@todo Fix ni-agree synchronising label sets
      if (cl->type == CLAIM_Niagree)
	{
	  int r_scan;

	  // Scan each role (except the current one) and pick out the last prec events.
	  r_scan = 0;
	  while (r_scan < sys->rolecount)
	    {
	      // Only other roles
	      if (r_scan != r1)
		{
		  // Scan fully
		  int ev_scan;
		  Term t_buf;

		  t_buf = NULL;
		  ev_scan = 0;
		  while (ev_scan < sys->roleeventmax)
		    {
		      // if this event preceds the claim, replace the label term
		      if (BIT
			  (prec + rowsize * index (r_scan, ev_scan),
			   claim_index))
			{
			  Roledef rd;

			  rd = roledef_re (r_scan, ev_scan);
			  if (rd->label != NULL)
			    {
			      t_buf = rd->label;
			    }
			}
		      ev_scan++;
		    }
		  // Store only the last label
		  if (t_buf != NULL)
		    {
		      sys->synchronising_labels =
			termlistAddNew (sys->synchronising_labels, t_buf);
		    }
		}
	      r_scan++;
	    }
	}

#ifdef DEBUG
      // Porparam = 100 (weirdness) [x][cc][debug] can turn of the synchronising label sets (override).
      if (switches.switchP == 100)
	{
	  termlistDelete (sys->synchronising_labels);
	  sys->synchronising_labels = NULL;
	  warning
	    ("Emptied synchronising labels set manually because --pp=100.");
	}
#endif
      // Check for empty stuff
      //@todo This is for debugging, mainly.
      if (cl->prec == NULL)
	{
	  if (inTermlist (CLAIMS_dep_prec, cl->type))
	    {
	      /* this claim depends on prec, but it is empty! */

	      cl->warnings = true;
	      globalError++;
	      eprintf ("warning: claim with label ");
	      termPrint (cl->label);
	      eprintf (" of role ");
	      termPrint (cl->rolename);
	      eprintf (" has an empty prec() set.\n");
	      globalError--;
	    }
	}
      else
	{
#ifdef DEBUG
	  if (DEBUGL (3))
	    {
	      Protocol p;

	      eprintf ("Preceding label set for r:%i, ev:%i = ", r1, ev1);
	      termlistPrint (cl->prec);
	      eprintf (", involving roles ");
	      termlistPrint (cl->roles);
	      eprintf (", from protocol ");
	      p = (Protocol) cl->protocol;
	      termPrint (p->nameterm);
	      eprintf ("\n");
	    }
#endif
	}

      // Proceed to next claim
      cl = cl->next;
    }

  /*
   * Cleanup
   */
  free (eventlabels);
  FREE (prec);

#ifdef DEBUG
  if (DEBUGL (2))
    {
      eprintf ("Synchronising labels set: ");
      termlistPrint (sys->synchronising_labels);
      eprintf ("\n");
    }
#endif

}

//! Check unused variables
/**
 * Some of this code is duplicated in the code that computes the role variables, so
 * that should be cleaned up some day. TODO.
 */
void
checkRoleVariables (const System sys, const Protocol p, const Role r)
{
  Termlist vars;
  Termlist declared;

  int process_event (Roledef rd)
  {
    if (rd->type == RECV)
      {
	vars = termlistAddVariables (vars, rd->from);
	vars = termlistAddVariables (vars, rd->to);
	vars = termlistAddVariables (vars, rd->message);
      }
    return 1;
  }

  /* Gather all variables occurring in the recvs */
  vars = NULL;
  roledef_iterate_events (r->roledef, process_event);

  /* Now, all variables for this role should be in the recvs */
  declared = r->declaredvars;
  while (declared != NULL)
    {
      if (!inTermlist (vars, declared->term))
	{
	  if (switches.check)
	    {
	      // Warning
	      globalError++;
	      eprintf ("warning: variable ");
	      termPrint (declared->term);
	      eprintf (" was declared in role ");
	      termPrint (p->nameterm);
	      eprintf (",");
	      termPrint (r->nameterm);
	      eprintf (" but never used in a recv event.\n");
	      globalError--;
	    }
	}
      declared = declared->next;
    }

  termlistDelete (vars);
}

//! Check unused variables
/**
 * This is checked per role
 */
void
checkUnusedVariables (const System sys)
{
  Protocol p;

  p = sys->protocols;
  while (p != NULL)
    {
      Role r;
      r = p->roles;
      while (r != NULL)
	{
	  checkRoleVariables (sys, p, r);
	  r = r->next;
	}
      p = p->next;
    }
}

//! Is a role well-formed?
/**
 * In line with the 2012 book, we check only that variables occur first in
 * receives. This is needed to guarantee that the instantiated terms are ground
 * (and hence, traces contain run terms).
 *
 * Returns true if the role is well-formed, false otherwise.
 *
 * The function outputs its own error messages, but does not (sys.)exit. This
 * should be done by the calling function, in order to collect a complete error
 * report for all roles.
 */
int
WellFormedRole (const System sys, Protocol p, Role r)
{
  Termlist tl;
  int allOkay;

  allOkay = true;
  for (tl = r->variables; tl != NULL; tl = tl->next)
    {
      if (!inTermlist (p->rolenames, tl->term))
	{
	  Roledef rd;

	  rd = firstEventWithTerm (r->roledef, tl->term);
	  if (rd->type != RECV)
	    {
	      // Not well-formed
	      globalError++;
	      error_pre ();
	      eprintf ("Protocol ");
	      termPrint (p->nameterm);
	      eprintf (", role ");
	      termPrint (r->nameterm);
	      eprintf (" is not well-formed: the variable '");
	      termPrint (tl->term);
	      eprintf ("' should occur first in a receive event.\n");
	      globalError--;

	      // Store
	      allOkay = false;
	    }
	}
    }
  return allOkay;
}

//! Well-formedness check
void
checkWellFormed (const System sys)
{
  int allOkay;

  allOkay = true;

  int thisRole (Protocol p, Role r)
  {
    allOkay = allOkay && WellFormedRole (sys, p, r);
    return true;
  }

  iterateRoles (sys, thisRole);
  if (allOkay == false)
    {
      error
	("The protocol specification does not meet the well-formedness condition.");
    }
}

//! Check matching role defs
int
checkEventMatch (const Roledef rd1, const Roledef rd2,
		 const Termlist rolenames)
{
  if (!isTermEqual (rd1->from, rd2->from))
    {
      return false;
    }
  if (!isTermEqual (rd1->to, rd2->to))
    {
      return false;
    }
  if (!checkRoletermMatch (rd1->message, rd2->message, rolenames))
    {
      return false;
    }
  return true;
}

//! Check label matchup for protocol p,r, roledef rd (which is a recv)
/**
 * Any send with the same label should match
 */

void
checkLabelMatchThis (const System sys, const Protocol p, const Role recvrole,
		     const Roledef recvevent)
{
  Role sendrole;
  int found;

  found = 0;
  sendrole = p->roles;
  while (sendrole != NULL)
    {
      Roledef event;

      event = sendrole->roledef;
      while (event != NULL)
	{
	  if (event->type == SEND)
	    {
	      if (isTermEqual (event->label, recvevent->label))
		{
		  // Same labels, so they should match up!
		  if (!checkEventMatch (event, recvevent, p->rolenames))
		    {
		      globalError++;
		      eprintf ("error: [%i]", recvevent->lineno);
		      if (sys->protocols != NULL)
			{
			  if (sys->protocols->next != NULL)
			    {
			      eprintf (" Protocol ");
			      termPrint (sys->protocols->nameterm);
			    }
			}
		      eprintf (" events for label ");
		      termPrint (event->label);
		      eprintf (" do not match, in particular: \n");
		      eprintf ("error: [%i] ", event->lineno);
		      roledefPrint (event);
		      eprintf (" does not match\n");
		      eprintf ("error: [%i] ", recvevent->lineno);
		      roledefPrint (recvevent);
		      eprintf ("\n");
		      error_die ();
		      globalError--;
		    }
		  else
		    {
		      found++;
#ifdef DEBUG
		      if (DEBUGL (2))
			{
			  eprintf ("Matching up label ");
			  termPrint (event->label);
			  eprintf (" to match: ");
			  roledefPrint (event);
			  eprintf (" <> ");
			  roledefPrint (recvevent);
			  eprintf ("\n");
			}
#endif
		    }
		}
	    }
	  event = event->next;
	}
      sendrole = sendrole->next;
    }

   //How many did we find?
   //* 1 is normal, more is interesting (branching?)
   //* 0 is not good, nobody will send it
  if (found == 0)
    {
      globalError++;
      eprintf ("error: [%i] for the recv event ", recvevent->lineno);
      roledefPrint (recvevent);
      eprintf (" of protocol ");
      termPrint (p->nameterm);
      eprintf
	(" there is no corresponding send event (with the same label and matching content). Start the label name with '!' if this is intentional.\n");
      error_die ();
      globalError--;
    }
}

//! Check label matchup for protocol p

void
checkLabelMatchProtocol (const System sys, const Protocol p)
{
  // For each recv label the sends should match
  Role r;

  r = p->roles;
  while (r != NULL)
    {
      Roledef rd;

      rd = r->roledef;
      while (rd != NULL)
	{
	  if (rd->type == RECV)
	    {
	      // We don't check all, if they start with a bang we ignore them.
	      Labelinfo li;

	      li = label_find (sys->labellist, rd->label);
	      if (li != NULL)
		{
		  if (!li->ignore)
		    {
		      checkLabelMatchThis (sys, p, r, rd);
		    }
		}
	      else
		{
		  globalError++;
		  eprintf
		    ("error: [%i] cannot determine label information for ",
		     rd->lineno);
		  roledefPrint (rd);
		  eprintf ("\n");
		  error_die ();
		  globalError--;
		}
	    }
	  rd = rd->next;
	}
      r = r->next;
    }
}

//! Check label matchup
void
checkLabelMatching (const System sys)
{
  Protocol p;

  // For each protocol
  p = sys->protocols;
  while (p != NULL)
    {
      checkLabelMatchProtocol (sys, p);
      p = p->next;
    }
}

//! Preprocess after system compilation
void
preprocess (const System sys)
{
  /*
   * Add default terms afterwards
   */
  specialTermInitAfter (sys);

  /* 
   * Clean up keylevels
   * */
  symbol_fix_keylevels ();

  /*
   * init some counters
   */
  sys->rolecount = compute_rolecount (sys);
  sys->roleeventmax = compute_roleeventmax (sys);
  /*
   * compute preceding label sets
   */
  compute_prec_sets (sys);
  /*
   * for now, we do not check whether labels match up
   */
  //checkLabelMatching (sys);
  /*
   * check for ununsed variables
   */
  if (switches.check)
    {
      checkUnusedVariables (sys);
    }
  /*
   * Initial knowledge
   */
  if (sys->knowledgedefined)
    {
      initialIntruderKnowledge (sys);
    }
  /*
   * compute hidelevels
   *
   * Needs to be done *after* the initial intruder knowledge derivation.
   */
  hidelevelCompute (sys);
  /*
   * Check well-formedness
   */
  checkWellFormed (sys);
}
