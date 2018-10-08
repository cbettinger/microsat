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

## Original License(s)
### The MIT License

Original work: Copyright © 2014-2018 Marijn Heule  
Contributions: Copyright © 2018 Armin Biere

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
