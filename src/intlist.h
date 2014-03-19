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

#ifndef INTLIST
#define INTLIST

//! int list structure node
struct intlist_struct
{
  struct intlist_struct *next;	//!< pointer to next node
  int value;			//!< the entry
};

typedef struct intlist_struct *IntList;	//!< pointer to int list node

IntList intlist_create (int value);
IntList intlist_forward (IntList list);
IntList intlist_insert (IntList list, int value);
IntList intlist_delete (IntList list);
int in_intlist (IntList list, int value);
void intlist_destroy (IntList list);
IntList intlist_shift (IntList list, int n);
int intlist_length (IntList list);

#endif
