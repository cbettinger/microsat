# microsat
[microsat](https://github.com/marijnheule/microsat) is a simple CDCL SAT solver by Marijn Heule and Armin Biere.

This fork adds the following features:
* Check *buildability* of a partial assignment, i.e. the satisfiability of a SAT problem with a explicit partial assignment and all undecided variables implicitely set to false
* Generate a *configuration*: Infer all consequent variable decisions based on a partial assignment of the SAT problem variables

## Build
	./configure && make

## Build and Install
	./configure && sudo make install

## Usage
### Print usage
	microsat

### Version info
	microsat --version

### Check satisfiability of a DIMACS encoded SAT problem
	microsat DIMACS_FILE

### Check buildability of a partial assignment
	microsat --check DIMACS_FILE

### Generate a configuration and check buildability of a partial assignment
	microsat --config DIMACS_FILE

### DIMACS file
The partial assignment of variables is denoted as DIMACS comment lines which have to be added before the problem line:

	c d<NUMBER_OF_DEAD_VARIABLES> <DEAD_VARIABLES>
	c v<NUMBER_OF_ASSIGNED_VARIABLES> <ASSIGNED_VARIABLES>

For example:

	c d1 26
	c v4 5 -7 18 -20
	p cnf ...
