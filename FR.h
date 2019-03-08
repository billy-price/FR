#ifndef FR_H
#define FR_H

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>

#include "equivalence.h"
#include "bryant.h"
#include "bryantPrint.h"
#include "var.h"

#define VAR_TO_REP(v) do {v+=VAR_SHIFT;} while (0)
#define VAR_TO_VAL(v) do {v-=VAR_SHIFT;} while (0)

typedef struct {
    Equivalence *F;
    node *R;
} FR_t;

FR_t *make_fr(Equivalence *F, node *R);

void fr_print(FILE *stream, FR_t *fr);

Equivalence *equiv_then_or_else(int pivot_var, Equivalence *T, Equivalence *E);

Equivalence *extract_equivs(node *R);

Equivalence *extract_equivs_wrt(Equivalence *F, node *R);

node *remove_entailments(Equivalence *F, node *R);

node *minimise(Equivalence *F, node *R);

// Compute canonical FR with semantic function equivalent to sem(F) & sem(R)
FR_t *canon_wrt(Equivalence *F, node *R);

FR_t *canon_robdd(node *R);

// Assumes F is flattened and root_var is positive
// Makes an ROBDD representing a single equivalence set
// and possibly it's opposite equivalence set
node *make_single_equiv_robdd(Equivalence *F, int root_var);

node *robdd_parallel_and(node **ROBDDs, int num_robdds);

node *robdd_parallel_or(node **ROBDDs, int num_robdds);

node *equiv_to_robdd(Equivalence *F);

node *fr_to_robdd(FR_t *fr);

FR_t *fr_glb(FR_t *A, FR_t *B);

FR_t *fr_lub(FR_t *A, FR_t *B);

FR_t *fr_negate(FR_t *fr);

/*
SWI_PROLOG FUNCTIONS
*/

FR_t *fr_implies(FR_t *A, FR_t *B);

FR_t *fr_projectThresh(int thresh, FR_t *fr);

FR_t *fr_variableRep(int var);

FR_t *fr_glb_array(int n, int arr[]);

FR_t *fr_renameArray(FR_t *fr, int count, int mapping[]);

FR_t *fr_reverseRenameArray(FR_t *fr, int count, int mapping[]);

FR_t *fr_iff_conj_array(int v0, int n, int arr[]);

FR_t *fr_projected_glb(int c, FR_t *A, FR_t *B) ;

bitset fr_vars_entailed(FR_t *fr);

int fr_max_variable(void);

#endif