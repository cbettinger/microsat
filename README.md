# microsat
[microsat](https://github.com/marijnheule/microsat) is a simple CDCL SAT solver, originally created by Marijn Heule and Armin Biere.

This fork adds the following features:
* Deduce variable decisions by propagating a (partial) assignment of the SAT problem variables
* Check the status of a (partial) assignment of the SAT problem variables
	* `INVALID`: The problem will evaluate to *false* regarding the partial assignment.
	* `INCOMPLETE`: The partial assignment is neither `INVALID` nor `BUILDABLE`.
	* `BUILDABLE`: The problem will evaluate to *true* after completing the assignment by setting all undecided variables implicitely to *false*.

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

### Propagate an assignment
	microsat --propagate DIMACS_FILE

### Check status of an assignment
	microsat --status DIMACS_FILE

### DIMACS file
The partial assignment is denoted as a DIMACS comment line which has to be added somewhere before the problem line:

	c v<NUMBER_OF_ASSIGNED_VARIABLES> <ASSIGNED_VARIABLES>

In order to work the solver needs to know the "dead" variables, i.e. variables that are always *false*. This could be determined internally but would increase runtime radically (especially if executed multiple times with the same SAT problem). Therefore they are presumed:
	
	c d<NUMBER_OF_DEAD_VARIABLES> <DEAD_VARIABLES>
	
For example:

	c v4 5 -7 18 -20
	c d1 26
	p cnf ...

Three demo files (one for each status described above) can be found in the *test* subdirectory.
