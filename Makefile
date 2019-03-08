# # # # # # #
# Makefile for assignment 2
#
# created May 2018
# Matt Farrugia <matt.farrugia@unimelb.edu.au>
#

CC     = gcc
CFLAGS = -Wall -std=c99 -g
# modify the flags here ^
EXE    = FR_main
OBJ    = FR.o equivalence.o bryant.o bryantPrint.o frPrint.o
# add any new object files here ^

# top (default) target
all: $(EXE)

# how to link executable
$(EXE): $(OBJ)
	$(CC) $(CFLAGS) -o $(EXE) $(OBJ)

# other dependencies
FR.o: FR.h bryant.h equivalence.h bryantPrint.h
equivalence.o: bryant.h equivalence.h
bryant.o: bryant.h var.h
frPrint.o: frPrint.h FR.h equivalence.h

# ^ add any new dependencies here (for example if you add new modules)


# phony targets (these targets do not represent actual files)
.PHONY: clean cleanly all CLEAN

# `make clean` to remove all object files
# `make CLEAN` to remove all object and executable files
# `make cleanly` to `make` then immediately remove object files (inefficient)
clean:
	rm -f $(OBJ)
CLEAN: clean
	rm -f $(EXE)
cleanly: all clean
