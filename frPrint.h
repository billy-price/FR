#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>
#include <stdint.h>

#include "FR.h"
#include "bryantPrint.h"

#define PRINT_TO_ROBDD 0

void fr_printOut(FILE *stream, FR_t *fr);