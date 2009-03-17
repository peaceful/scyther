/*
 * Scyther : An automatic verifier for security protocols.
 * Copyright (C) 2007-2009 Cas Cremers
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

#ifndef SWITCHES
#define SWITCHES

#include "term.h"
#include "system.h"

void switchesInit ();
void switchesDone ();

//! Command-line switches structure
struct switchdata
{
  // Command-line
  int argc;
  char **argv;

  // Methods
  int match;			//!< Matching type.
  int tupling;			//!< Tupling is by default 0: right-associative, optionally 1: left-associative.

  // Pruning and Bounding
  int prune;			//!< Type of pruning.
  int maxproofdepth;		//!< Maximum proof depth
  int maxtracelength;		//!< Maximum trace length allowed
  int runs;			//!< The number of runs as in the switch
  char *filterProtocol;		//!< Which claim should be checked?
  char *filterLabel;		//!< Which claim should be checked?
  int maxAttacks;		//!< When not 0, maximum number of attacks
  int maxOfRole;		//!< When not 0, maximum number of instances of each unique (non intruder) role

  // Arachne
  int heuristic;		//!< Goal selection method for Arachne engine
  int maxIntruderActions;	//!< Maximum number of intruder actions in the semitrace (encrypt/decrypt)
  int agentTypecheck;		//!< Check type of agent variables in all matching modes
  int concrete;			//!< Swap out variables at the end.
  int initUnique;		//!< Default allows duplicate terms in rho (init) 
  int respUnique;		//!< Default allows duplicate terms in rho (resp)
  int intruder;			//!< Enable intruder actions (default)
  int agentUnfold;		//!< Explicitly unfold for N honest agents and 1 compromised iff > 0
  int abstractionMethod;	//!< 0 means none, others are specific modes
  int useAttackBuffer;		//!< Use temporary file for attack storage
  int partnerDefinition;	//!< 0: temporally close, 1: matching histories, 2: SID definition
  int requireSynch;		//!< 0: it's not an attack if you don't synchronize
  int checkMatchingLabels;	//!< default is to check matching labels

  // Adversary type
  int LKRnotgroup;		//!< anybody outside the group
  int LKRactor;			//!< KCI
  int LKRactorrnsafe;		//!< KCI with rn safe
  int LKRafter;			//!< perfect forward secrecy
  int LKRaftercorrect;		//!< weak perfect forward secrecy
  int LKRrnsafe;		//!< weaker perfect forward secrecy
  int SKR;			//!< session-key reveal (for others)
  int SSR;			//!< SSR others 
  int RNR;			//!< RNR reveal
  int forceRegular;		//!< Force considering regular run
  // Filters
  int SSRfilter;		//!< SSR filtering on nonces (implies SSR)
  int RNRinfer;			//!< Do full state for RNR contents: takes whatever SSR would do.
  int SSRinfer;			//!< SSR manual / inferred
  int markFullSession;		//!< Not a real switch but a marker

  // Misc
  int switchP;			//!< A multi-purpose integer parameter, passed to the partial order reduction method selected.
  int experimental;		//!< Experimental stuff goes here until it moves into main stuff.
  int removeclaims;		//!< Remove any claims in the spdl file
  int addreachableclaim;	//!< Adds 'reachable' claims to each role
  int addallclaims;		//!< Adds all sorts of claims to the roles
  int check;			//!< Check protocol correctness
  int expert;			//!< Expert mode

  // Output
  int output;			//!< From enum outputs: what should be produced. Default ATTACK.
  int report;
  int reportClaims;		//!< Enable claims report
  int xml;			//!< xml output
  int dot;			//!< dot output
  int human;			//!< human readable
  int reportMemory;		//!< Memory display switch.
  int reportTime;		//!< Time display switch.
  int countStates;		//!< Count states
  int extendNonReads;		//!< Show further events in arachne xml output.
  int extendTrivial;		//!< Show further events in arachne xml output, based on knowledge underapproximation. (Includes at least the events of the nonreads extension)
  int plain;			//!< Disable color output on terminal
  int monochrome;		//!< Disable colors in dot output
  int lightness;		//!< Lightness increment 0-100
  int clusters;			//!< Enable clusters in output
  int exitCodes;		//!< Enable verbose exit codes
  int reportCompromise;		//!< Report compromise additions and exit
};

extern struct switchdata switches;	//!< pointer to switchdata structure

FILE *openFileSearch (char *filename, FILE * reopener);

#endif
