/*
 * attack_check.h
 *
 *  Created on: Mar 10, 2015
 *      Author: nguyen
 */

#ifndef ATTACK_CHECK_H_
#define ATTACK_CHECK_H_
#include "system.h"
#include "role.h"
#include "system.h"
#include "arachne.h"
#include "error.h"
#include "binding.h"
#include "switches.h"
#include <stdlib.h>
void initModelCheck(System);

struct runinfo
{
	  Protocol protocol;		//!< Protocol of this run.
	  Role role;			//!< Role of this run.
	  Term lastevent;			//!< Current execution point in the run (the label of the last event)
} runinfo;
typedef struct runinfo *Runinfo;
void copyRuns(System);
void mapRuns(Claimlist, int*, int*);
#endif /* ATTACK_CHECK_H_ */
