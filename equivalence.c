#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

#include "equivalence.h"
#include "bryant.h"
#include "var.h"

#define HAS_CONTRADICTION(F) (F->pars[TRUE_VAR]==FALSE_VAR)

#if !defined(max)
#define max(a,b) ((a)<(b) ? (b) : (a))
#endif
#if !defined(min)
#define min(a,b) ((a)<(b) ? (a) : (b))
#endif

#define MAX_DEP(F,G) (max(F->max_dep,G->max_dep))

#define NO_DEPENDENCE (-1)

#define SWAP_PTRS(type,a,b) do {type tmp; tmp=a; a=b; b=tmp;} while(0)

bitset emptyset;

/*---------------------------
CONSTRUCTION
-----------------------------*/

Equivalence *alloc_equiv(void) {
    return (Equivalence *) malloc(sizeof(Equivalence));
}

Equivalence *make_identity_equiv(void) {
    Equivalence *F = alloc_equiv();
    F->pars[FALSE_VAR] = FALSE_VAR;
    F->pars[TRUE_VAR] = TRUE_VAR;
    F->max_dep = NO_DEPENDENCE;
    return F;
}

Equivalence *make_equiv_copy(Equivalence *F) {
    if (IS_TRIVIAL_EQUIV(F)) return F;
    Equivalence *G = alloc_equiv();
    int i;
    for (i=0; i<=F->max_dep; i++) G->pars[i] = F->pars[i];
    G->max_dep = F->max_dep;
    return G; 
}

void write_equiv_copy(Equivalence *src, Equivalence *dest) {
    if (IS_TRIVIAL_EQUIV(src)) {dest = src; return;}

    int i;
    for (i=0; i<=src->max_dep; i++) dest->pars[i] = src->pars[i];
    dest->max_dep = src->max_dep;
}

/*---------------------------
HELPERS
-----------------------------*/

// built from find algorithm on union-find_root wikipedia page
// finds the least variable x such that x<->v
// Assumes non-trivial Equivalence
int find(Equivalence *F, int var){

    if (var > F->max_dep) return var;

    int par=F->pars[var];
    
    // case: par is not a root
    if (F->pars[par]!=par) {
        // set parent of var to root of par
        F->pars[var] = find(F, par);
    }
    
    // parent of var is now var's root
    return F->pars[var];
}

// Are x and y equivalent variables?
// Does F |= (x<->y) ?
bool are_equiv(Equivalence *F, int x, int y){
    return (x==y || find(F, x) == find(F, y));
}


bool is_entailed(Equivalence *F, int v) {
    return are_equiv(F,v,TRUE_VAR);
}

bool is_disentailed(Equivalence *F, int v) {
    return are_equiv(F,v,FALSE_VAR);
}

// send every parent branch directly to root
void flatten(Equivalence *F) {
    if (IS_TRIVIAL_EQUIV(F)) return;
    int i;
    for (i=F->max_dep; i>=2; i--) find(F, i);
}

void expand_max_dep(Equivalence *F, int new_max_dep) {
    int i;

    for (i=F->max_dep+1; i<new_max_dep; ++i) {
        F->pars[i] = i;
    }

    F->max_dep = new_max_dep;
}

void shrink_max_dep(Equivalence *F) {
    
    int i = F->max_dep;
    while (i>=0 && F->pars[i]==i) --i;
    F->max_dep = i;
}

bool equiv_equals(Equivalence *F, Equivalence *G) {
    if (IS_TRIVIAL_EQUIV(F) || IS_TRIVIAL_EQUIV(G)) return F==G;

    int i;
    if (F->max_dep != G->max_dep) return false;

    for (i=0; i<=F->max_dep; i++) {
        if (F->pars[i]!=G->pars[i]) return false;
    }
    return true;
}

bitset equiv_vars_entailed(Equivalence *F) {
    bitset entailed = emptyset;
    if (IS_TRIVIAL_EQUIV(F)) {
        if (F==FALSE_EQUIV) BITSET_UNIVERSE(entailed);
        return entailed;
    }

    int i;

    for (i = F->max_dep; i>=2; --i) {
        if (IS_ENTAILED(F, i)) BITSET_ADD_ELEMENT(entailed, i-VAR_SHIFT);
    }
    
    return entailed;
}

void compress_path_via(Equivalence *F, int v, int v_root) {
    int i;
    for (i=F->max_dep; i>v; i--) {
        if (F->pars[i]==v) F->pars[i] = v_root;
    }
}


/*---------------------------
MAIN ALGS
-----------------------------*/

// unify the set containing x and the set containing y
// collapses the equivalence to identity and returns false if contradiction arises, true otherwise
Equivalence *onion(Equivalence *F, int x, int y) {
    int x_root, y_root;

    if (IS_TRIVIAL_EQUIV(F)){
        if (F == FALSE_EQUIV || x == y) return F;
        else F = make_identity_equiv();

        x_root = x;
        y_root = y;

    } else {
        x_root = find(F,x);
        y_root = find(F,y);
    }
    
    
    if (x_root < y_root) {
        F->pars[y_root] = x_root;
        if (y_root > F->max_dep) expand_max_dep(F, y_root);
        else compress_path_via(F, y_root, x_root);

    } else if (x_root > y_root) {
        F->pars[x_root] = y_root;
        if (x_root > F->max_dep) expand_max_dep(F, x_root);
        else compress_path_via(F, x_root, y_root);
    }
    
    if (HAS_CONTRADICTION(F)) return FALSE_EQUIV;

    return F;
}

Equivalence *init_onion(int x, int y) {
    return onion(TRUE_EQUIV, x, y);
}


//-----------------------------------------------------
// Equivalence Operations
//-----------------------------------------------------

Equivalence *equiv_and(Equivalence *F, Equivalence *G) {
    if (IS_TRIVIAL_EQUIV(F)) {
        return F == FALSE_EQUIV ? FALSE_EQUIV : make_equiv_copy(G);
    } else if (IS_TRIVIAL_EQUIV(G)) {
        return G == FALSE_EQUIV ? FALSE_EQUIV : make_equiv_copy(F);
    }

    Equivalence *H = make_identity_equiv();

    // turn parents into roots
    //flatten(F); flatten(G);

    // Ensure that F->max_dep <= G->max_dep to simplify next 2 for loops
    if (F->max_dep > G->max_dep) SWAP_PTRS(Equivalence *,F,G);

    H->max_dep = G->max_dep;
    int i;
    // Both F and G have correctly defined arrays up to F->max_dep (inclusive)
    for (i=0; i<=F->max_dep; i++) {

        H->pars[i] = i;

        if (FALSE_EQUIV == onion(H, F->pars[i], G->pars[i])) {
            free(H);
            return FALSE_EQUIV;
        }
        H->pars[i] = find(H, F->pars[i]);

        /*
        // case: H->pars[F->pars[i]] is the new smallest root for i, F->pars[i] and G->pars[i] in H
        if (H->pars[F->pars[i]] <= H->pars[G->pars[i]]) {
            H->pars[H->pars[G->pars[i]]] = H->pars[F->pars[i]];
            H->pars[i] = H->pars[F->pars[i]];
        
        // case: H->pars[G->pars[i]] is the new smallest root for i, F->pars[i] and G->pars[i] in H
        } else {
            H->pars[H->pars[F->pars[i]]] = H->pars[G->pars[i]];
            H->pars[i] = H->pars[G->pars[i]];
        }
        
        // Check for contradiction
        if HAS_CONTRADICTION(H) {
            free(H);
            return FALSE_EQUIV;
        }*/
    }

    // We are beyond the max_dep for F, so we pretend all F parents are themselves
    // Therefore F adds no more equivalences, so we just get the rest from G
    for (i=F->max_dep+1; i<= G->max_dep; i++) {
        H->pars[i] = i;
        H->pars[i] = H->pars[G->pars[i]]; // This links i to G[i], by linking directly to it's root in H
    }


    flatten(H);

    return H;
}

static int common_roots[MAXVAR][MAXVAR];

void init_common_roots(int max_dep) {
    int i,j;
    for (i=0; i<=max_dep; ++i) {
        for (j=0; j<=max_dep; ++j) {
            common_roots[i][j] = INVALID_VAR;
        }
    }
}

Equivalence *equiv_or(Equivalence *F, Equivalence *G) {
    if (IS_TRIVIAL_EQUIV(F)) {
        return F==TRUE_EQUIV ? F : G;
    } else if (IS_TRIVIAL_EQUIV(G)) {
        return G==TRUE_EQUIV ? G : F;
    }

    Equivalence *H = make_identity_equiv();
    H->max_dep = min(F->max_dep, G->max_dep);

    init_common_roots(H->max_dep);

    // turn parents into roots
    //flatten(F); flatten(G);
    
    int i, common_root;
    
    for (i=0; i<=H->max_dep; i++) {
        
        // F and G agree on equivalence to root
        if (F->pars[i] == G->pars[i]) {
            H->pars[i] = F->pars[i];
        } else {
            // Check hash table for smaller equivalent variable in H
            // (a variable j<i that has identical F->pars[j] G->pars[j] pair)
            common_root = common_roots[F->pars[i]][G->pars[i]];
            
            if (common_root!=INVALID_VAR) {
                H->pars[i] = common_root;
            } else {
                common_roots[F->pars[i]][G->pars[i]] = i;
                H->pars[i] = i;
            }
        }
    }

    shrink_max_dep(H);

    if (H->max_dep < 0) {
        free(H);
        return TRUE_EQUIV;
    } else {
        return H;
    }
}

Equivalence *equiv_or_destructive(Equivalence *F, Equivalence *G) {
    if (IS_TRIVIAL_EQUIV(F)) {
        return F==TRUE_EQUIV ? F : G;
    } else if (IS_TRIVIAL_EQUIV(G)) {
        return G==TRUE_EQUIV ? G : F;
    }

    Equivalence *H = make_identity_equiv();
    H->max_dep = min(F->max_dep, G->max_dep);

    init_common_roots(H->max_dep);

    // turn parents into roots
    //flatten(F); flatten(G);
    
    int i, common_root;
    

    for (i=0; i<=H->max_dep; i++) {
        
        // F and G agree on equivalence to root
        if (F->pars[i] == G->pars[i]) {
            H->pars[i] = F->pars[i]; // write equivalence to H
            F->pars[i] = i; G->pars[i] = i; //remove connection to root from F and G
        
        } else {
            common_root = common_roots[F->pars[i]][G->pars[i]];

            // case: pair seen before
            if (common_root!=INVALID_VAR) {
                H->pars[i] = common_root;  // give H connection between them
                F->pars[i] = i; G->pars[i] = i; //remove connection from F and G
                
            } else /* case: pair not seen before */{
                common_roots[F->pars[i]][G->pars[i]] = i;
                H->pars[i] = i;
                // leave smaller root knowledge in F and G
            }
        }

    }

    shrink_max_dep(H);

    if (H->max_dep < 0) {
        free(H);
        return TRUE_EQUIV;
    } else {
        return H;
    }
}

// Intersects T and E, while adding anything that is entailed by T and disentailed by E
// as an equivalent variable to root var

// T and E should NOT be trivial equivalences (Neither should be)

/* Rough relationship between arguments
       (root_var)
        /     \
       T      E
*/
Equivalence *equiv_then_or_else(int root_var, Equivalence *T, Equivalence *E) {
    Equivalence *H = make_identity_equiv();
    H->max_dep = min(T->max_dep, E->max_dep);

    init_common_roots(H->max_dep);

    // turn parents into roots
    //flatten(T); flatten(E);
    
    int i, common_root;
    
    int temp_H_max_dep = H->max_dep; // This could change during loop
    for (i=0; i<=temp_H_max_dep; i++) {
        
        // case: Then and Else equivs agree on i's least equiv var
        if (T->pars[i] == E->pars[i]) {
            H->pars[i] = T->pars[i];
        
        } else if (IS_ENTAILED(T,i) && IS_DISENTAILED(E,i)) {
            // Therefore (root_var <-> i)
            if (root_var < i) {
                H->pars[i] = H->pars[root_var];
            } else if (i < root_var) {
                if (root_var > H->max_dep) expand_max_dep(H, root_var);
                H->pars[root_var] = H->pars[i] = i;
            } else { /* i==root_var */
                H->pars[i] = i;
            }
        } else {
            
            // Then and Else disagree on root
            
            // Check hash table for smaller equivalent variable in H (var j<i that has identical T->pars[j] E->pars[j])
            common_root = common_roots[T->pars[i]][E->pars[i]];
            
            // Write it as root, if it was there
            if (common_root!=INVALID_VAR) {
                H->pars[i] = common_root;
            // Otherwise write i as the least equivalent variable for this key pair
            } else {
                common_roots[T->pars[i]][E->pars[i]] = i;
                H->pars[i] = i;
            }
        }
    }

    shrink_max_dep(H);

    if (H->max_dep < 0) {
        free(H);
        return TRUE_EQUIV;
    } else {
        return H;
    }
}

//-----------------------------------------------------
// Other algorithms
//-----------------------------------------------------

Equivalence *equiv_renameArray(Equivalence *F, int count, int mapping[]) {
    if (IS_TRIVIAL_EQUIV(F)) return F;
    
    //flatten(F);---------------------------------------------------------------------------------------------

    if (F->max_dep < count) expand_max_dep(F, count);

    // apply the mapping
    int i, child_map, par_map;
    for (i=2; i<=count; i++) {
        if ((child_map = mapping[i]) == UNUSED_MAPPING_COPY) {
            child_map = i;
        }

        if (F->pars[i] <= 1) {
            par_map = F->pars[i];
        }
        else if ((par_map = mapping[F->pars[i]]) == UNUSED_MAPPING_COPY) {
            par_map = F->pars[i];
        } else {
            par_map = mapping[F->pars[i]];
        }

        F->pars[child_map] = par_map;
    }

    // redirect vars to their smallest root
    for (i=2; i<=count; i++) {
        F->pars[i] = F->pars[F->pars[i]]; // update parent to root
        if (F->pars[i] > i) { // case: i should actually be the root of its current parent
            F->pars[F->pars[i]] = i;
            F->pars[i] = i;
        }
    }

    shrink_max_dep(F);

    if (F->max_dep < 0) {
        free(F);
        return TRUE_EQUIV;
    } else {
        return F;
    }
}

//-----------------------------------------------------
// Deconstructing algorithms
//-----------------------------------------------------

//remove from F any equivalence relation of the form
//v <-> x (for x=/=v)
//i.e. remove other variables from v's set
void detach(Equivalence *F, int v) {

    int i;
    
    if (F->pars[v]==v) {

        //find the smallest equivalent variable bigger than v
        i = v+1;
        while (i<=F->max_dep && find(F,i)!=v) i++;

        // case: i is the least equivalent variable to v
        if (i<=F->max_dep) {
            
            int j;
            // attach all remaining equivalent vars to new root
            for (j=i; j<=F->max_dep; j++) {
                if (find(F,j)==v) {
                    F->pars[j] = i;
                }
            }
        }
        // Otherwise no other equivalent variable - done.


    // case: v isn't a root
    } else {
        
        // ensure every variable that could be linked through v
        // is now directly connected to the common root (which isn't v)
        for (i=v; i<=F->max_dep; i++) find(F,i);
        
        F->pars[v]=v;
    }
}

void equiv_project_thresh(int thresh, Equivalence *F) {
    if (IS_TRIVIAL_EQUIV(F)) return;

    F->max_dep = min(F->max_dep, thresh);
}

//-----------------------------------------------------
// Printing algorithms
//-----------------------------------------------------


// print roots of each variable
void root_print(FILE *stream, Equivalence *F) {
    if (F == FALSE_EQUIV) {fprintf(stream, "FALSE EQUIV"); return;}
    if (F == TRUE_EQUIV)  {fprintf(stream, "TRUE EQUIV"); return;}
    int i;
    
    flatten(F);
    printf("Roots:\n");
    for (i=0; i<=F->max_dep; i++) {
        fprintf(stream, "var: %d, root: %d\n", i, F->pars[i]);
    }
}

// Not that efficient
// Prints equivalent sets, headed by root
void equiv_print(FILE *stream, Equivalence *F) {
    if (F == FALSE_EQUIV) {fprintf(stream, "FALSE EQUIV"); return;}
    if (F == TRUE_EQUIV)  {fprintf(stream, "TRUE EQUIV"); return;}

    flatten(F);

    int i, j;
    bitset seen = emptyset;
    bitset curr_set;
    
    fprintf(stream, "def vars  :( ");
    for (i=2; i<=F->max_dep; ++i) {
        if (IS_ENTAILED(F,i)) {
            BITSET_ADD_ELEMENT(seen, i);
            fprintf(stream, "%d ", i-VAR_SHIFT);
        } else if (IS_DISENTAILED(F,i)) {
            BITSET_ADD_ELEMENT(seen, i);
            fprintf(stream, "~%d ", i-VAR_SHIFT);
        }
    }
    fprintf(stream, ")");

    fprintf(stream, "\nequiv sets:(");
    // print one set per unique root (except singleton sets)
    for (i=2; i<=F->max_dep; i++) {
        if (BITSET_IS_MEMBER(seen,i)) continue;
        
        BITSET_CLEAR(curr_set);

        for (j=i+1; j <= F->max_dep; j++) {
            
            if (ARE_EQUIV(F,i,j)) {
                BITSET_ADD_ELEMENT(curr_set, j);
            }
        }

        if (!BITSET_EMPTY(curr_set)) {
            fprintf(stream, " { %d ", i-VAR_SHIFT);
            for (j=i+1; j <= F->max_dep; j++) {
                if (BITSET_IS_MEMBER(curr_set, j)) {
                    BITSET_ADD_ELEMENT(seen, j);
                    fprintf(stream, "%d ", j-VAR_SHIFT);
                }
            }
            fprintf(stream, "} ");
        }

        BITSET_ADD_ELEMENT(seen, i);
    }
    fprintf(stream, ")");
}