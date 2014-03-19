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

/**
 *@file intlist.c
 * Integer list type
 *
 * A linked list for integers
 */

#include <stdbool.h>

#include "intlist.h"
#include "mymalloc.h"

//! Make a node
IntList
intlist_create (int value)
{
  IntList newlist;

  newlist = (IntList) malloc (sizeof (struct intlist_struct));
  newlist->next = NULL;
  newlist->value = value;
  return newlist;
}

//! Forward list
IntList
intlist_forward (IntList list)
{
  if (list == NULL)
    {
      return NULL;
    }
  else
    {
      while (list->next != NULL)
	{
	  list = list->next;
	}
      return list;
    }
}

//! Add element to list, inserting it just before the current node.
/**
 * @returns the head of the list
 */
IntList
intlist_insert (IntList list, int value)
{
  IntList newnode;

  newnode = intlist_create (value);
  newnode->next = list;
  return newnode;
}

//! Destroy a node
/**
 * @returns the head of the list
 */
IntList
intlist_delete (IntList list)
{
  if (list != NULL)
    {
      IntList postnode;

      postnode = list->next;
      free (list);
      return postnode;
    }
  else
    {
      return NULL;
    }
}

//! Test if it's already in the list, using integer equality.
/**
 *@returns The boolean result.
 */
int
in_intlist (IntList list, int compvalue)
{
  while (list != NULL)
    {
      if (list->value == compvalue)
	{
	  return true;
	}
      list = list->next;
    }
  return false;
}

//! Destroy (shallow)
void
intlist_destroy (IntList list)
{
  while (list != NULL)
    {
      IntList node;

      node = list;
      list = list->next;
      free (node);
    }
}

//! Shift n positions to the right
IntList
intlist_shift (IntList list, int n)
{
  while (n > 0 && list != NULL)
    {
      list = list->next;
      n--;
    }
  return list;
}

//! Determine length of list 
int
intlist_length (IntList list)
{
  int n;

  n = 0;
  while (list != NULL)
    {
      n++;
      list = list->next;
    }
  return n;
}
