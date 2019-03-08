#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>
#include <stdint.h>

#include "FR.h"
#include "bryantPrint.h"
#include "frPrint.h"


void fr_print(FILE *stream, FR_t *fr) {
    equiv_print(stream, fr->F); printf("\n");
    fprintf(stream, "robdd     :"); printOut(stream, fr->R);
}

void fr_to_robdd_print(FILE *stream, FR_t *fr) {
    printOut(stream, fr_to_robdd(fr));
}

void fr_printOut(FILE *stream, FR_t *fr) {
    if (PRINT_TO_ROBDD) fr_to_robdd_print(stream, fr);
    else fr_print(stream, fr);
}
