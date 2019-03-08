#ifndef EQUIV_H
#define EQUIV_H

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

#include "bryant.h"

#define INVALID_VAR (-1)
#define FALSE_VAR 0
#define TRUE_VAR 1

#define FALSE_EQUIV ((Equivalence *) 0)
#define TRUE_EQUIV ((Equivalence *) 1)

#define IS_TRIVIAL_EQUIV(F) (INTCAST(F) <= 1)

// variable with value i is equivalent to its smaller value parent at parents[i]
typedef struct {
    int pars[MAXVAR]; // x is equivalent to pars[x], where pars[x] < x
    int max_dep;      // maximum x such that pars[x] is not x
} Equivalence;

/*---------------------------
CONSTRUCTION
-----------------------------*/

Equivalence *make_identity_equiv(void);

Equivalence *make_total_equiv(void);

Equivalence *make_equiv_copy(Equivalence *F);

void write_equiv_copy(Equivalence *src, Equivalence *dest);

Equivalence *init_onion(int x, int y);

Equivalence *init_entail_vars(int n, int vars[]);

/*---------------------------
HELPERS
-----------------------------*/

// built from find algorithm on union-find_root wikipedia page
// finds the least variable x such that x<->v
int find(Equivalence *F, int var);

// Are x and y equivalent variables?
// Does F |= (x<->y) ?
bool are_equiv(Equivalence *F, int x, int y);

bool is_entailed(Equivalence *F, int v);

bool is_disentailed(Equivalence *F, int v);

// send every parent branch directly to root
void flatten(Equivalence *F);

bool equiv_equals(Equivalence *F, Equivalence *G);

bitset equiv_vars_entailed(Equivalence *F);

/*---------------------------
MAIN ALGS
-----------------------------*/

// unify the set containing x and the set containing y
// collapses the equivalence to identity and returns false if contradiction arises, true otherwise
Equivalence *onion(Equivalence *F, int x, int y);

/*---------------------------
MACRO Functions
-----------------------------*/
#define ARE_EQUIV(F,x,y) (x == y || \
                          F == FALSE_EQUIV || \
                          (F!=TRUE_EQUIV && find(F, x) == find(F, y)) )

#define IS_ENTAILED(F,v) ARE_EQUIV(F,TRUE_VAR,v)

#define IS_DISENTAILED(F,v) ARE_EQUIV(F,FALSE_VAR,v)

#define IS_DEFINITE(F,v) (IS_ENTAILED(F,v) || IS_DISENTAILED(F,v))

#define SET_ENTAILED(F,v) onion(F,TRUE_VAR,v)

#define SET_DISENTAILED(F,v) onion(F,FALSE_VAR,v)

// returns Equivalence *
#define INIT_ENTAILED(v) init_onion(TRUE_VAR, v)

// returns Equivalence *
#define INIT_DISENTAILED(v) init_onion(FALSE_VAR, v)

//-----------------------------------------------------
// Equivalence Operations
//-----------------------------------------------------

// try union on F: {1,3,4}, G: {2,3,4}
Equivalence *equiv_and(Equivalence *F, Equivalence *G);

Equivalence *equiv_or(Equivalence *F, Equivalence *G);

Equivalence *equiv_or_destructive(Equivalence *F, Equivalence *G);

//-----------------------------------------------------
// Other algorithms
//-----------------------------------------------------

Equivalence *equiv_renameArray(Equivalence *F, int count, int mapping[]);

//-----------------------------------------------------
// Deconstructing algorithms
//-----------------------------------------------------

//remove from F any equivalence relation of the form
//v <-> x (for x=/=v)
//i.e. remove other variables from v's set
void detach(Equivalence *F, int v);

void equiv_project_thresh(int thresh, Equivalence *F);

// remove all equivalence relations between the variables in set v
// i.e. divide v's set into singleton sets
void dissolve_set(Equivalence *F, int v);

//-----------------------------------------------------
// Printing algorithms
//-----------------------------------------------------

// print roots of each variable
void root_print(FILE *stream, Equivalence *F);

// Not that efficient
// Prints equivalent sets, headed by root
void equiv_print(FILE *stream, Equivalence *F);

#endif