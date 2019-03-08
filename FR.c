#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>
#include <stdint.h>

#include "FR.h"
#include "bryant.h"
#include "equivalence.h"
#include "var.h"

#if !defined(max)
#define max(a,b) ((a)<(b) ? (b) : (a))
#endif
#if !defined(min)
#define min(a,b) ((a)<(b) ? (a) : (b))
#endif

/* automatically initialized to all 0 bits: */
bitset emptyset;

//--------------------

/********************************************************************

		      Caching of computed values

 ********************************************************************/

#define DECLARE_CACHE(op,type)			\
static type op##_computed_cache[COMPUTED_TABLE_SIZE]

//---------------------------------------------------------------
// Unary Node Cache - maps ROBDD's to ROBDD's under some op
//---------------------------------------------------------------

#define UNARY_NODE_HASH(a) \
      (INTCAST(a) % COMPUTED_TABLE_SIZE)

typedef struct {
    node *f;
    node *result;
} unary_cache_entry;

#define DECLARE_UNARY_CACHE_ENTRY unary_cache_entry *cache;

#define UPDATE_UNARY_CACHE(n,robdd,op)	\
do {					\
	cache->f = n;			\
	cache->result = robdd;		\
} while (0)

#define TRY_UNARY_CACHE(n,op)						\
do {									\
	cache = &((op##_computed_cache)[UNARY_NODE_HASH(n)]);		\
	if (cache->f==(n)) {						\
	    return cache->result;					\
	}								\
} while (0)

//---------------------------------------------------------------
// Extraction Cache - maps ROBDD's to Equivalences
//---------------------------------------------------------------

typedef struct {
    node *r;
    Equivalence result;
} extraction_cache_entry;

#define DECLARE_EXTRACT_CACHE_ENTRY extraction_cache_entry *cache;

#define UPDATE_EXTRACT_CACHE(R,F,op)	\
do {					\
	cache->r = R;			\
    if (IS_TRIVIAL_EQUIV(F)) {  \
        if (F==FALSE_EQUIV) cache->result.pars[TRUE_VAR] = FALSE_VAR;   \
        else {cache->result.pars[TRUE_VAR] = TRUE_VAR; cache->result.max_dep=(-1);}  \
    }   \
	write_equiv_copy(F, &cache->result);		\
} while (0)

#define TRY_EXTRACT_CACHE(R,op)						\
do {									\
	cache = &((op##_computed_cache)[UNARY_NODE_HASH(R)]);	\
	if (cache->r==R) {				\
        if (cache->result.max_dep == (-1)) return TRUE_EQUIV;   \
        else if (cache->result.pars[TRUE_VAR]==FALSE_VAR) return FALSE_EQUIV;   \
        else return make_equiv_copy(&cache->result);					\
	}								\
} while (0)

DECLARE_CACHE(extract_equivs,extraction_cache_entry);

//---------------------------------------------------------------
/*
Useful Equivalence pointer and bitsets
*/

static Equivalence *known;
static bitset entailed;
static bitset disentailed;

/*---------------------------
CONSTRUCTION
-----------------------------*/

FR_t *make_fr(Equivalence *F, node *R) {
    FR_t *fr = malloc(sizeof *fr);
    assert(fr);
    fr->F = F;
    fr->R = R;
    return fr;
}

FR_t *make_fr_copy(FR_t *fr) {
    FR_t *new_fr = malloc(sizeof *fr);
    assert(new_fr);
    new_fr->F = make_equiv_copy(fr->F);
    new_fr->R = fr->R;
    return new_fr;
}

bool is_true_rep(FR_t *fr) {
    return (fr->F == TRUE_EQUIV && fr->R == one);
}

bool is_false_rep(FR_t *fr) {
    if (fr->F == FALSE_EQUIV) {
        assert(fr->R == zero && "FALSE_EQUIV with non-zero robdd");
        return true;
    } else {
        assert(fr->R != zero && "zero robdd with non-FALSE_EQUIV");
        return false;
    }
}

FR_t *fr_true_rep(void) {
    return make_fr(TRUE_EQUIV, one);
}

FR_t *fr_false_rep(void) {
    return make_fr(FALSE_EQUIV, zero);
}

/*---------------------------
HELPER FUNCTIONS
-----------------------------*/

Equivalence *extract_equivs_aux(node *R) {
    if (IS_TERMINAL(R)) {
        if (R==zero) return FALSE_EQUIV;
        else return TRUE_EQUIV;
    }

    Equivalence *result;
    DECLARE_EXTRACT_CACHE_ENTRY
    TRY_EXTRACT_CACHE(R,extract_equivs);
    
    if (R->fa == zero) {
        result = SET_ENTAILED(extract_equivs_aux(R->tr), R->value);
    } else if (R->tr == zero) {
        result = SET_DISENTAILED(extract_equivs_aux(R->fa), R->value);
    } else {
        Equivalence *equiv_then = extract_equivs_aux(R->tr);
        Equivalence *equiv_else = extract_equivs_aux(R->fa);
        if (equiv_then == TRUE_EQUIV || equiv_else == TRUE_EQUIV) {
            result = TRUE_EQUIV;
        } else {
            result = equiv_then_or_else(R->value, equiv_then, equiv_else);
        }
    }

    UPDATE_EXTRACT_CACHE(R, result, extract_equivs);

    return result;
}

Equivalence *extract_equivs(node *R) {
    known = TRUE_EQUIV;
    return extract_equivs_aux(R);
}

// The known equivalence is analagous to the TRUE_EQUIV - they are externally sourced equivalences
// makes equiv_and unecessary later without sacrificing much time here at all
// also returns the exact known pointer (unmodified) if no equivalences/entailments are found
Equivalence *extract_equivs_wrt_aux(node *R) {
    if (IS_TERMINAL(R)) {
        if (R==zero) return FALSE_EQUIV;
        else return known;
    }

    if (R->value > known->max_dep) {
        return equiv_and(known, extract_equivs_aux(R));
    }

    int lead_var = find(known, R->value);

    if (lead_var == TRUE_VAR  || BITSET_IS_MEMBER(entailed   , lead_var)) return extract_equivs_wrt_aux(R->tr);
    if (lead_var == FALSE_VAR || BITSET_IS_MEMBER(disentailed, lead_var)) return extract_equivs_wrt_aux(R->fa);

    BITSET_ADD_ELEMENT(entailed, lead_var);
    Equivalence *equiv_then = extract_equivs_wrt_aux(R->tr);
    BITSET_REMOVE_ELEMENT(entailed, lead_var);

    BITSET_ADD_ELEMENT(disentailed, lead_var);
    Equivalence *equiv_else = extract_equivs_wrt_aux(R->fa);
    BITSET_REMOVE_ELEMENT(disentailed, lead_var);
    
    if (equiv_else == FALSE_EQUIV) {
        if (IS_ENTAILED(equiv_then, R->value)) {
            return equiv_then;
        } else {
            if (equiv_then == known) equiv_then = make_equiv_copy(equiv_then); // don't let known be modified
            return SET_ENTAILED(equiv_then, R->value);  // known & R entails R->value
        }
    
    } else if (equiv_then == FALSE_EQUIV) {
        if (IS_DISENTAILED(equiv_else, R->value)) {
            return equiv_else;
        } else {
            if (equiv_else == known) equiv_else = make_equiv_copy(equiv_else); // don't let known be modified
            return SET_DISENTAILED(equiv_else, R->value);  // known & R entails R->value
        }
    
    } else if (equiv_then == known && equiv_else == known) {
        return known;
    } else {
        if (!IS_ENTAILED(equiv_then, R->value)) {
            if (equiv_then == known) equiv_then = make_equiv_copy(equiv_then); // don't let known be modified
            SET_ENTAILED(equiv_then, R->value);  // known & R entails R->value
        }
        if (!IS_DISENTAILED(equiv_else, R->value)) {
            if (equiv_else == known) equiv_else = make_equiv_copy(equiv_else); // don't let known be modified
            SET_DISENTAILED(equiv_else, R->value);  // known & R entails R->value
        }
        Equivalence *result = equiv_or(equiv_then, equiv_else);
        return equiv_equals(result,known) ? known : result;
    }
}

Equivalence *extract_equivs_wrt(Equivalence *F, node *R) {
    known = F;
    if (IS_TRIVIAL_EQUIV(F)) return F == FALSE_EQUIV ? FALSE_EQUIV : extract_equivs(R);
    BITSET_CLEAR(entailed);BITSET_CLEAR(disentailed);
    return extract_equivs_wrt_aux(R);
}


node *minimise_aux(node *R) {

    if (IS_TERMINAL(R)) return R;

    int lead_var = find(known, R->value);

    if      (lead_var == TRUE_VAR  || BITSET_IS_MEMBER(entailed   , lead_var)) return minimise_aux(R->tr);
    else if (lead_var == FALSE_VAR || BITSET_IS_MEMBER(disentailed, lead_var)) return minimise_aux(R->fa);

    //otherwise no path decision or entailment above

    BITSET_ADD_ELEMENT(entailed, lead_var);
    node *new_true = minimise_aux(R->tr);
    BITSET_REMOVE_ELEMENT(entailed, lead_var);

    BITSET_ADD_ELEMENT(disentailed, lead_var);
    node *new_false = minimise_aux(R->fa);
    BITSET_REMOVE_ELEMENT(disentailed, lead_var);

    return make_node(R->value, new_true, new_false);
}

node *minimise(Equivalence *F, node *R) {
    if (IS_TRIVIAL_EQUIV(F)) return F==TRUE_EQUIV ? R : zero;
    else {
        BITSET_CLEAR(entailed); BITSET_CLEAR(disentailed);
        known = F;
        return minimise_aux(R);
    }
}


node *self_minimise_aux(node *R) {
    if (IS_TERMINAL(R)){
        return R;
    }

    // case: R->value has a smaller equivalent variable in the full robdd
    if (find(known,R->value)!=R->value) {
        // one of the children must be zero
       return R->fa == zero ? self_minimise_aux(R->tr) : self_minimise_aux(R->fa);
    } else {
        return make_node(R->value,self_minimise_aux(R->tr), self_minimise_aux(R->fa));
    }
}

// Assumes R |= R_equivs
node *self_minimise(Equivalence *R_equivs, node *R) {
    if (IS_TRIVIAL_EQUIV(R_equivs)) return R;
    
    known = R_equivs;
    return self_minimise_aux(R);
}


// Compute canonical FR with semantic function equivalent to sem(F) & sem(R)
FR_t *canon_wrt(Equivalence *F, node *R) {
    if (IS_TRIVIAL_EQUIV(F)) {
        if (F==FALSE_EQUIV) {
            R = zero;
        } else { /* F==TRUE_EQUIV */
            return canon_robdd(R);
        }
    } else {
        F = extract_equivs_wrt(F,R);
        R = minimise(F, R);
    }

    return make_fr(F,R);
}

FR_t *canon_robdd(node *R){
    Equivalence *F;
    F = extract_equivs(R);
    R = self_minimise(F, R);
    
    return make_fr(F, R);
}


// Assumes num_robdds >=1
node *robdd_parallel_and(node **ROBDDs, int num_robdds) {

    if (num_robdds == 1) return ROBDDs[0];

    int i;
    
    // the number of ROBDDs needed for the next recursive call
    // (equal to the current number of non-terminal robdds)
    int next_num_robdds = 0;
    // the minimum dependent variable amongst the non-terminal ROBDDs
    int min_var = MAXVAR+1;
    
    // Calculate next_num_robdds and min_var
    for (i=0; i<num_robdds; i++) {
        if (ROBDDs[i]==zero) return zero; // trivial case
        else if (ROBDDs[i]!=one) {        // 
            min_var = min(min_var, ROBDDs[i]->value);
            ++next_num_robdds;
        }
    }
    
    // case: every node was a one node
    if (next_num_robdds == 0) return one;
    
    // at this point every node is either a one or var node (with at least one var node)

    // Allocate space needed for recursion
    node **rec_ROBDDs  = malloc(next_num_robdds * sizeof(node *));
    
    // Write all the non-terminal nodes needed for true child recursive call
    int next_node_pos = 0;
    for (i=0; i<num_robdds; i++) {
        if (ROBDDs[i]!=one) { // ignore true nodes
            // If they have the minimum value, write the true child
            if (ROBDDs[i]->value == min_var) {
                rec_ROBDDs[next_node_pos]  = ROBDDs[i]->tr;
            } else /*otherwise write itself*/ {
                rec_ROBDDs[next_node_pos]  = ROBDDs[i];
            }
            ++next_node_pos;
        }
    }
    
    // get the AND of all the ROBDDs with all the minimum var nodes replaced by their true childs
    node* true_child = robdd_parallel_and(rec_ROBDDs, next_num_robdds);
    
    // Write all the non-terminal nodes needed for false child recursive call
    next_node_pos=0;
    for (i=0; i<num_robdds; i++) {
        if (ROBDDs[i]!=one) {
            // If they have the minimum value, write the true child
            if (ROBDDs[i]->value == min_var) {
                rec_ROBDDs[next_node_pos]  = ROBDDs[i]->fa;
            } // otherwise - itself is already there!
            ++next_node_pos;
        }
    }
    
    // get the AND of all the ROBDDs with all the minimum var nodes replaced by their true childs
    node *false_child = robdd_parallel_and(rec_ROBDDs, next_num_robdds);

    return make_node(min_var, true_child, false_child);
}

node *equiv_to_robdd(Equivalence *F) {
    if (F == FALSE_EQUIV) return zero;
    if (F == TRUE_EQUIV)  return one;
    flatten(F);

    node **equiv_trues =  malloc((F->max_dep+1)*sizeof(*equiv_trues));
    node **equiv_falses = malloc((F->max_dep+1)*sizeof(*equiv_falses));
    node *definites = one;

    int i;
    int num_equivs = 0;

    bitset roots = emptyset;

    for (i=F->max_dep; i>=2; i--) {
        
        if (IS_ENTAILED(F,i)) {
            definites = make_node(i, definites, zero);
        } else if (IS_DISENTAILED(F,i)) {
            definites = make_node(i, zero, definites);
        } else if (F->pars[i] != i){

            // case: haven't seen this root yet, need to initialise one node at root index
            if (!BITSET_IS_MEMBER(roots, F->pars[i])) {
                equiv_trues[F->pars[i]] = equiv_falses[F->pars[i]] = one;
                BITSET_ADD_ELEMENT(roots, F->pars[i]);
                num_equivs++;
            }

            equiv_trues[F->pars[i]]  = make_node(i, equiv_trues[F->pars[i]], zero);
            equiv_falses[F->pars[i]] = make_node(i, zero, equiv_falses[F->pars[i]]);
        }
    }

    node **equiv_robdds = malloc((1+num_equivs)*sizeof(node *));
    equiv_robdds[0] = definites;
    int j=1;
    for (i=2; i <= F->max_dep; i++) {
        // case: i is the root of a non-singleton equivalence set
        if (BITSET_IS_MEMBER(roots, i)) {
            equiv_robdds[j++] = make_node(i, equiv_trues[i], equiv_falses[i]);
        }
    }

    return robdd_parallel_and(equiv_robdds, 1+num_equivs);
}

node *fr_to_robdd(FR_t *fr) {
    return glb(equiv_to_robdd(fr->F), fr->R);
}

node *robdd_parallel_or(node **ROBDDs, int num_robdds) {
    int i;
    
    // the number of ROBDDs needed for the next recursive call
    // (equal to the current number of non-terminal robdds)
    int next_num_robdds = 0;
    // the minimum dependent variable amongst the non-terminal ROBDDs
    int min_var = MAXVAR+1;
    
    // Calculate correct next_num_robdds and min_var
    for (i=0; i<num_robdds; i++) {
        if (ROBDDs[i]==one) return one; // trivial case
        else if (ROBDDs[i]!=zero) {
            min_var = min(min_var, ROBDDs[i]->value);
            next_num_robdds++;
        }
    }
    
    // case: every node was a zero node
    if (next_num_robdds == 0) return zero;
    
    // at this point every node is either a zero or var node (with at least one var node)
    
    // Allocate space needed for recursion
    node **rec_ROBDDs  = malloc(next_num_robdds*sizeof(*rec_ROBDDs));
    
    
    // Write all the non-terminal nodes needed for true child recursive call
    int next_node_pos = 0;
    for (i=0; i<num_robdds; i++) {
        if (ROBDDs[i]!=zero) {
            // If they have the minimum value, write the true child
            if (ROBDDs[i]->value == min_var) {
                rec_ROBDDs[next_node_pos]  = ROBDDs[i]->tr;
            } else /*otherwise write itself*/ {
                rec_ROBDDs[next_node_pos]  = ROBDDs[i];
            }
            ++next_node_pos;
        }
    }
    
    // get the OR of all the ROBDDs with all the minimum var nodes replaced by their true childs
    node* true_child = robdd_parallel_or(rec_ROBDDs, next_num_robdds);
    
    // Write all the non-terminal nodes needed for false child recursive call
    next_node_pos=0;
    for (i=0; i<num_robdds; i++) {
        if (ROBDDs[i]!=zero) {
            // If they have the minimum value, write the false child
            if (ROBDDs[i]->value == min_var) {
                rec_ROBDDs[next_node_pos]  = ROBDDs[i]->fa;
            } // otherwise - itself is already there!
            ++next_node_pos;
        }
    }
    
    // get the OR of all the ROBDDs with all the minimum var nodes replaced by their true childs
    node *false_child = robdd_parallel_or(rec_ROBDDs, next_num_robdds);
    
    return make_node(min_var, true_child, false_child);
}

/*---------------------------
 FR Operations
-----------------------------*/
FR_t *fr_glb(FR_t *A, FR_t *B) {

    if (A->R == one) {
        return canon_wrt(equiv_and(A->F, B->F), B->R);
    } else if (B->R == one) {
        return canon_wrt(equiv_and(A->F, B->F), A->R);
    }
    
    Equivalence *F = equiv_and(A->F, B->F);
    node *new_AR = A->R;
    node *new_BR = B->R;

    if (A->F == TRUE_EQUIV) {
        if (B->F != TRUE_EQUIV) {
            F = extract_equivs_wrt(F, A->R);
            new_AR = minimise(F, A->R);
        }
    } else {
        F = extract_equivs_wrt(F, B->R);
        if (F == FALSE_EQUIV) return fr_false_rep();

        if (B->F != TRUE_EQUIV) {
            F = extract_equivs_wrt(F, A->R);
            if (F == FALSE_EQUIV) return fr_false_rep();
            new_AR = minimise(F, A->R);
        }

        new_BR = minimise(F, B->R);
    }
     
    node *R = glb(A->R, B->R);

    return canon_wrt(F,R); //might be able to just extract_equivs from R (cache version), minimise, then conjoin with F
}

FR_t *fr_lub(FR_t *A, FR_t *B) {
    if (is_true_rep(A) || is_false_rep(B)) return A;
    if (is_true_rep(B) || is_false_rep(A)) return B;

    // Intersection of equivalences are stored in F
    // remaining forgotten equivalences are left in A->F and B->F (at most one per equivalence class in F)
    Equivalence *F = equiv_or_destructive(A->F, B->F);

    node *R = and_or_and(equiv_to_robdd(A->F),A->R,
                          equiv_to_robdd(B->F),B->R);

    return make_fr(F,R);
}

// crappy
FR_t *fr_negate(FR_t *fr) {
    if (is_true_rep(fr)) return fr_false_rep();
    if (is_false_rep(fr)) return fr_true_rep();
    return canon_robdd(nand(equiv_to_robdd(fr->F),fr->R));
}

FR_t *fr_implies(FR_t *A, FR_t *B) {
    if      (is_true_rep(A)) return make_fr_copy(B);
    else if (is_false_rep(A) || is_true_rep(B)) return fr_true_rep();
    else if (is_false_rep(B)) return fr_negate(A);

    return canon_robdd(
                and_implies_and(
                    equiv_to_robdd(A->F), A->R,
                    equiv_to_robdd(B->F), B->R));
}

/*
SWI_PROLOG FUNCTIONS
*/

FR_t *fr_projectThresh(int thresh, FR_t *fr) {
    VAR_TO_REP(thresh);

    equiv_project_thresh(thresh, fr->F);
    fr->R = projectThresh(thresh, fr->R);
    return fr;
}


#define VARS_TO_REP(arr,n) \
do {    \
    int i;  \
    for (i=0; i<n; ++i) VAR_TO_REP(arr[i]);     \
} while (0)

FR_t *fr_variableRep(int var) {
    VAR_TO_REP(var);
    return make_fr(init_onion(TRUE_VAR, var), one);
}

FR_t *fr_glb_array(int n, int arr[]) {
    Equivalence *F = make_identity_equiv();
    int i;
    for (i=0; i<n; i++) {
        F->pars[arr[i]+VAR_SHIFT] = TRUE_VAR;
        F->max_dep = max(F->max_dep, arr[i]+VAR_SHIFT);
    }
    return make_fr(F, one);
}

FR_t *fr_renameArray(FR_t *fr, int count, int mapping[]) {
    int i;
    for (i=0; i<=count; ++i) {
        if (mapping[i]!=UNUSED_MAPPING_COPY) {
            VAR_TO_REP(mapping[i]);
        }
    }
    fr->F = equiv_renameArray(fr->F,count,mapping);
    fr->R = renameArray(fr->R,count,mapping);

    return fr;
}

FR_t *fr_reverseRenameArray(FR_t *fr, int count, int mapping[]) {

    int i, val, max;
    int rev_map[MAXVAR];


    /* NB:  four -1 bytes is the same as a -1 word */
	memset(rev_map, -1, sizeof(rev_map));
	for (i=1,max=-1; i<=count; ++i) { //------------------------------------------ Why starting at i=1?
	    rev_map[(val=mapping[i])] = i;
	    if (max < val) max = val;
	}

    return fr_renameArray(fr, max, rev_map);
}

FR_t *fr_iff_conj_array(int v0, int n, int arr[]) {
    VAR_TO_REP(v0);
    VARS_TO_REP(arr, n);

    if (n==1) return make_fr(init_onion(v0,*arr), one);
    else return make_fr(TRUE_EQUIV, iff_conj_array(v0, n, arr));
}

FR_t *fr_projected_glb(int c, FR_t *A, FR_t *B) {
    if (is_false_rep(A) || is_true_rep(B)) return fr_projectThresh(c, A);
    if (is_false_rep(B) || is_true_rep(A)) return fr_projectThresh(c, B);

    Equivalence *F = equiv_and(A->F, B->F);
    node *new_AR = A->R;
    node *new_BR = B->R;

    if (A->F == TRUE_EQUIV) {
        if (B->F != TRUE_EQUIV) {
            F = extract_equivs_wrt(F, A->R);
            new_AR = minimise(F, A->R);
        }
    } else {
        F = extract_equivs_wrt(F, B->R);
        if (F == FALSE_EQUIV) return fr_false_rep();

        if (B->F != TRUE_EQUIV) {
            F = extract_equivs_wrt(F, A->R);
            if (F == FALSE_EQUIV) return fr_false_rep();
            new_AR = minimise(F, A->R);
        }

        new_BR = minimise(F, B->R);
    }
     
    node *R = glb(A->R, B->R);

    FR_t *result = canon_wrt(F,R);

    return fr_projectThresh(c,result);
}

bitset fr_vars_entailed(FR_t *fr) {
    return equiv_vars_entailed(fr->F);
}

int fr_max_variable(void) {
    return MAXVAR - VAR_SHIFT;
}

FR_t *fr_abstract_unify(FR_t *fr, int v0, int n, int arr[], int thresh) {
    return fr_projected_glb(thresh, fr, fr_iff_conj_array(v0, n, arr));
}

int array_is_ordered(int array[], int size)
    {
	int i;
	int prev = array[1];

	for (i=2; i<=size; ++i) {
	    if (array[i] >= 0) { /* ignore negative elements */
		if (array[i] <= prev) return 0;
		prev = array[i];
	    }
	}
	return 1;
    }

int main(){
    return 0;
}