#ifndef BINDINGS
#define BINDINGS

#include "term.h"
#include "termmap.h"
#include "system.h"

//! Binding structure
/*
 * Idea is the ev_from *has to* precede the ev_to
 */
struct binding
{
  int done;			//!< Iff true, it is bound
  int blocked;			//!< Iff true, ignore it

  int run_from;			//!< origination run
  int ev_from;			//!< step in origination run

  int run_to;			//!< destination run
  int ev_to;			//!< step in destination run

  Term term;			//!< Binding term
  int level;			//!< ???
};

typedef struct binding *Binding;	//!< pointer to binding structure


void bindingInit (const System mysys);
void bindingDone ();

int node_count ();
int node_number (int run, int ev);
__inline__ int graph_nodes (const int nodes, const int run1, const int ev1,
			    const int run2, const int ev2);

int isOrderedBefore (const int run1, const int ev1, const int run2,
		     const int ev2);

void goal_graph_create ();


int binding_print (Binding b);
int valid_binding (Binding b);

int goal_add (Term term, const int run, const int ev, const int level);
int goal_add_fixed (Term term, const int run, const int ev, const int fromrun,
		    const int fromev);
void goal_remove_last (int n);
int goal_bind (const Binding b, const int run, const int ev);
void goal_unbind (const Binding b);
int binding_block (Binding b);
int binding_unblock (Binding b);
int labels_ordered (Termmap runs, Termlist labels);

int bindings_c_minimal ();

#endif
