# microsat

*Note*: This is a fork of [microsat](https://github.com/marijnheule/microsat) by Marijn Heule and Armin Biere.

## Build

	./configure && make

## Build and Install

	./configure && sudo make install

## Usage
### Version info

	microsat --version

### Solving a DIMACS encoded SAT problem
	microsat DIMACS_FILE

### Evaluate system decisions
    microsat --c DIMACS_FILE

### Evaluate buildability of a given configuration
    microsat --c_sat DIMACS_FILE

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
