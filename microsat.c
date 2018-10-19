#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum MODES																							// The application modes, set by command line options
{
	MODE_SOLVE = 0,
	MODE_PROPAGATE = 1,
	MODE_STATUS = 2
};

int MODE;

enum EXIT_CODES																						// The exit codes for the application
{
	ERROR = -1,
	OK = 0,
	SAT = 10,
	UNSAT = 20,
	BUILDABLE = 100,
	INCOMPLETE = 150,
	INVALID = 200
};

enum LITERAL_FLAGS																					// Flags for marking literals during solving process
{
	END = -9,
	MARK = 2,
	IMPLIED = 6
};

const int MEM_MAX = 1 << 30;																		// Maximal memory for the database: 2^30 Bytes = 1.073.741.824 Bytes = 1074 MBytes

struct solver																						// The variables in the solver struct are described in the init...() functions
{
	int *DB, mem_used, mem_fixed,
		nVars, nClauses, maxLemmas, nLemmas, nConflicts, nRestarts, fast, slow,
		*model, *next, *prev, *clauseBuffer, *reason, *falseStack, *forced, *false, *processed, *assigned, *first, head,
		nDeadVars, *deadVars, nAssignments, *assignments;
};

void addWatch(struct solver *S, int lit, int mem)													// Add a watch pointer to a clause containing lit
{
	S->DB[mem] = S->first[lit];																		// By updating the database and the pointers
	S->first[lit] = mem;
}

int evaluateClauses(struct solver *S)
{
	int clauseStatus = 1;

	int lit = *(S->processed++);
	int *watch = &S->first[lit];

	while (*watch != END)
	{
		int i, unit = 1;
		int *clause = (S->DB + *watch + 1);

		if (clause[-2] == 0)
			clause++;

		if (clause[0] == lit)
			clause[0] = clause[1];

		for (i = 2; unit && clause[i]; i++)
		{
			if (!S->false[clause[i]])
			{
				clause[1] = clause[i];
				clause[i] = lit;
				int store = *watch;
				unit = 0;
				*watch = S->DB[*watch];
				addWatch(S, clause[1], store);
			}
		}

		if (unit)
		{
			clause[1] = lit;
			watch = (S->DB + *watch);

			if (S->false[-clause[0]] || !S->false[clause[0]])
				continue;
			else
				return 0;
		}
	}

	return clauseStatus;
}

void assign(struct solver *S, int *reason, int forced)												// Make the first literal of the reason true
{
	int lit = reason[0];																			// Let lit be the first literal in the reason
	S->false[-lit] = forced ? IMPLIED : 1;															// Mark lit as true and IMPLIED if forced
	*(S->assigned++) = -lit;																		// Push it on the assignment stack
	S->reason[abs(lit)] = 1 + (int)((reason)-S->DB);												// Set the reason clause of lit
	S->model[abs(lit)] = (lit > 0);																	// Mark the literal as true in the model
}

int allVariablesAssigned(struct solver *S)
{
	int nVarsAssigned = 0;
	for (int i = -S->nVars; i <= S->nVars; i++)
	{
		if (S->false[i])
			nVarsAssigned++;
	}
	return nVarsAssigned == S->nVars;
}

int evaluateBuildability(struct solver *S)
{
	if (!allVariablesAssigned(S))
	{
		for (int i = 1; i <= S->nVars; i++)
		{
			if (!S->model[i] && !S->false[i])
			{
				int lemma = -i;
				assign(S, &lemma, 0);
				if (!evaluateClauses(S))
					return 0;
			}
		}
	}

	return 1;
}

int evaluateAssignment(struct solver *S)
{
	for (int i = 0; i < S->nAssignments; i++)
	{
		if ((S->assignments[i] < 0 && S->false[S->assignments[i]]) || (S->assignments[i] > 0 && S->false[S->assignments[i]]))
		{
			return 0;
		}

		for (int j = 0; j < S->nDeadVars; j++)
		{
			if (S->deadVars[j] == -S->assignments[i])
			{
				return 0;
			}
		}

		assign(S, &S->assignments[i], 1);
		if (!evaluateClauses(S))
		{
			return 0;
		}
	}

	return 1;
}

int checkStatus(struct solver *S)																	// Return status of a (partial) assignment
{
	if (!evaluateAssignment(S))
		return INVALID;
	else if (!evaluateBuildability(S))
		return INCOMPLETE;
	else
		return BUILDABLE;
}

void printImpliedDecisions(struct solver *S)														// Print all variable decisions implied by propagation
{
	printf("v");
	for (int i = 1; i <= S->nVars; i++)
	{
		if (S->model[i] && (S->false[-i] == IMPLIED))
		{
			printf(" %i", i);
		}
		else if (S->false[i] == IMPLIED)
		{
			printf(" %i", -i);
		}
	}
	printf("\n");
}

int *getMemory(struct solver *S, int mem_size)														// Allocate memory of size mem_size
{
	if (S->mem_used + mem_size > MEM_MAX)															// Exit if maximal memory is reached
		printf("c OUT OF MEMORY\n"), exit(ERROR);

	int *store = (S->DB + S->mem_used);																// Compute a pointer to the new memory location
	S->mem_used += mem_size;																		// Update the size of the used memory
	return store;																					// Return the pointer
}

int *addClause(struct solver *S, int *in, int size, int irr)										// Adds a clause stored in *in of size size
{
	int i, used = S->mem_used;				  														// Store a pointer to the beginning of the clause
	int *clause = getMemory(S, size + 3) + 2; 														// Allocate memory for the clause in the database

	{
		addWatch(S, in[0], used);																	// Two watch pointers to the datastructure
		addWatch(S, in[1], used + 1);
	}

	for (i = 0; i < size; i++)																		// Copy the clause from the buffer to the database
		clause[i] = in[i];
	clause[i] = 0;

	if (irr)																						// Update the statistics
		S->mem_fixed = S->mem_used;
	else
		S->nLemmas++;

	return clause;																					// Return the pointer to the clause is the database
}

int implied(struct solver *S, int lit)																// Check if lit(eral) is implied by MARK literals
{
	if (S->false[lit] > MARK)																		// If checked before return old result
		return (S->false[lit] & MARK);

	if (!S->reason[abs(lit)])																		// In case lit is a decision, it is not implied
		return 0;

	int *p = (S->DB + S->reason[abs(lit)] - 1); 													// Get the reason of lit(eral)
	while (*(++p))																					// While there are literals in the reason
	{
		if ((S->false[*p] ^ MARK) && !implied(S, *p))												// Recursively check if non-MARK literals are implied
		{
			S->false[lit] = IMPLIED - 1;															// Mark and return not implied (denoted by IMPLIED - 1)
			return 0;
		}
	}

	S->false[lit] = IMPLIED;																		// Mark and return that the literal is implied
	return 1;
}

void unassign(struct solver *S, int lit)															// Unassign the literal
{
	S->false[lit] = 0;
}

void bump(struct solver *S, int lit)																// Move the variable to the front of the decision list
{
	if (S->false[lit] != IMPLIED)																	// MARK the literal as involved if not a top-level unit
	{
		S->false[lit] = MARK;

		int var = abs(lit);																			// In case var is not already the head of the list
		if (var != S->head)
		{
			S->prev[S->next[var]] = S->prev[var];													// Update the prev link, and
			S->next[S->prev[var]] = S->next[var];													// Update the next link, and
			S->next[S->head] = var;																	// Add a next link to the head, and
			S->prev[var] = S->head;																	// Make var the new head
			S->head = var;
		}
	}
}

int *analyze(struct solver *S, int *clause)															// Compute a resolvent from falsified clause
{
	S->nRestarts++;																					// Bump restarts and update the statistic
	S->nConflicts++;

	while (*clause)																					// MARK all literals in the falsified clause
		bump(S, *(clause++));

	while (S->reason[abs(*(--S->assigned))])														// Loop on variables on falseStack until the last decision
	{
		if (S->false[*S->assigned] == MARK)															// If the tail of the stack is MARK
		{
			int *check = S->assigned;																// Pointer to check if first-UIP is reached
			while (S->false[*(--check)] != MARK) {													// Check for a MARK literal before decision
				if (!S->reason[abs(*check)])														// Otherwise it is the first-UIP so break
					goto build;
			}

			clause = S->DB + S->reason[abs(*S->assigned)];											// Get the reason and ignore first literal

			while (*clause)																			// MARK all literals in reason
				bump(S, *(clause++));
		}

		unassign(S, *S->assigned);																	// Unassign the tail of the stack
	}

build:;																								// Build conflict clause; Empty the clause buffer
	int size = 0, lbd = 0, flag = 0;

	int *p = S->processed = S->assigned;															// Loop from tail to front
	while (p >= S->forced)																			// Only literals on the stack can be MARKed
	{
		if ((S->false[*p] == MARK) && !implied(S, *p))												// If MARKed and not implied
		{
			S->clauseBuffer[size++] = *p;															// Add literal to conflict clause buffer
			flag = 1;
		}

		if (!S->reason[abs(*p)])																	// Increase LBD for a decision with a true flag
		{
			lbd += flag;
			flag = 0;
			if (size == 1)																			// And update the processed pointer
				S->processed = p;
		}
		S->false[*(p--)] = 1;																		// Reset the MARK flag for all variables on the stack
	}

	S->fast -= S->fast >> 5;																		// Update the fast moving average
	S->fast += lbd << 15;
	S->slow -= S->slow >> 15;																		// Update the slow moving average
	S->slow += lbd << 5;

	while (S->assigned > S->processed)																// Loop over all unprocessed literals
		unassign(S, *(S->assigned--));																// Unassign all lits between tail & head

	unassign(S, *S->assigned);																		// Assigned now equal to processed
	S->clauseBuffer[size] = 0;																		// Terminate the buffer (and potentially print clause)

	return addClause(S, S->clauseBuffer, size, 0);													// Add new conflict clause to redundant DB
}

int propagate(struct solver *S)																		// Performs unit propagation
{
	int forced = S->reason[abs(*S->processed)];														// Initialize forced flag
	while (S->processed < S->assigned)																// While unprocessed false literals
	{
		int lit = *(S->processed++);																// Get first unprocessed literal
		int *watch = &S->first[lit];																// Obtain the first watch pointer

		while (*watch != END)																		// While there are watched clauses (watched by lit)
		{
			int i, unit = 1;																		// Let's assume that the clause is unit
			int *clause = (S->DB + *watch + 1);														// Get the clause from DB

			if (clause[-2] == 0)
				clause++;																			// Set the pointer to the first literal in the clause

			if (clause[0] == lit)
				clause[0] = clause[1];																// Ensure that the other watched literal is in front

			for (i = 2; unit && clause[i]; i++)														// Scan the non-watched literals
				if (!S->false[clause[i]])															// When clause[i] is not false, it is either true or unset
				{
					clause[1] = clause[i];															// Swap literals
					clause[i] = lit;

					int store = *watch;																// Store the old watch
					unit = 0;
					*watch = S->DB[*watch];															// Remove the watch from the list of lit
					addWatch(S, clause[1], store);													// Add the watch to the list of clause[1]
				}

			if (unit)																				// If the clause is indeed unit
			{
				clause[1] = lit;																	// Place lit at clause[1] and update next watch
				watch = (S->DB + *watch);

				if (S->false[-clause[0]])															// If the other watched literal is satisfied continue
					continue;

				if (!S->false[clause[0]])															// If the other watched literal is falsified,
				{
					assign(S, clause, forced);														// A unit clause is found, and the reason is set
				}
				else
				{
					if (forced)																		// Found a root level conflict -> UNSAT
						return UNSAT;

					int *lemma = analyze(S, clause);												// Analyze the conflict return a conflict clause
					if (!lemma[1])																	// In case a unit clause is found, set forced flag
						forced = 1;

					assign(S, lemma, forced);														// Assign the conflict clause as a unit
					break;
				}
			}
		}
	}

	if (forced)																						// Set S->forced if applicable
		S->forced = S->processed;

	return SAT;																						// Finally, no conflict was found
}

void reduceDB(struct solver *S, int k)																// Removes "less useful" lemmas from DB
{
	while (S->nLemmas > S->maxLemmas)																// Allow more lemmas in the future
		S->maxLemmas += 300;
	S->nLemmas = 0;																					// Reset the number of lemmas

	int i;
	for (i = -S->nVars; i <= S->nVars; i++)															// Loop over the variables
	{
		if (i == 0)
			continue;

		int *watch = &S->first[i];																	// Get the pointer to the first watched clause
		while (*watch != END)																		// As long as there are watched clauses
			if (*watch < S->mem_fixed)																// Remove the watch if it points to a lemma
				watch = (S->DB + *watch);
			else																					// Otherwise (meaning an input clause) go to next watch
				*watch = S->DB[*watch];
	}

	int old_used = S->mem_used;																		// Virtually remove all lemmas
	S->mem_used = S->mem_fixed;

	for (i = S->mem_fixed + 2; i < old_used; i += 3)												// While the old memory contains lemmas
	{
		int count = 0, head = i;																	// Get the lemma to which the head is pointing
		while (S->DB[i])
		{
			int lit = S->DB[i++];																	// Count the number of literals
			if ((lit > 0) == S->model[abs(lit)])													// That are satisfied by the current model
				count++;
		}

		if (count < k)
			addClause(S, S->DB + head, i - head, 0);												// If the latter is smaller than k, add it back
	}
}

void restart(struct solver *S)																		// Perform a restart (i.e., unassign all variables)
{
	while (S->assigned > S->forced)																	// Remove all unforced false lits from falseStack
		unassign(S, *(--S->assigned));
	S->processed = S->forced;																		// Reset the processed pointer
}

int solve(struct solver *S)																			// Determine satisfiability
{
	int decision = S->head;																			// Initialize the solver
	for (;;)																						// Main solve loop
	{
		int old_nLemmas = S->nLemmas;																// Store nLemmas to see whether propagate adds lemmas

		if (propagate(S) == UNSAT)
			return UNSAT;																			// Propagation returns UNSAT for a root level conflict

		if (S->nLemmas > old_nLemmas)																// If the last decision caused a conflict
		{
			decision = S->head;																		// Then reset the decision heuristic to head
			if (S->fast > (S->slow / 100) * 125)													// If fast average is substantially larger than slow average
			{
				S->nRestarts = 0;																	// Then restart and update the averages
				S->fast = (S->slow / 100) * 125;
				restart(S);

				if (S->nLemmas > S->maxLemmas)														// Reduce the DB when it contains too many lemmas
					reduceDB(S, 6);
			}
		}

		while (S->false[decision] || S->false[-decision])											// As long as the temporary decision is assigned
		{
			decision = S->prev[decision];															// Replace it with the next variable in the decision list
		}

		if (decision == 0)																			// If the end of the list is reached
			return SAT;																				// Then a solution is found

		decision = S->model[decision] ? decision : -decision;										// Otherwise, assign the decision variable based on the model
		S->false[-decision] = 1;																	// Assign the decision literal to true
		*(S->assigned++) = -decision;																// And push it on the assigned stack
		decision = abs(decision);																	// Decisions have no reason clauses
		S->reason[decision] = 0;
	}
}

void propagateAssignment(struct solver *S)															// Propagate a (partial) assignment
{
	for (int i = 0; i < S->nDeadVars; i++)															// Assign dead variables
	{
		assign(S, &S->deadVars[i], 1);
	}
	propagate(S);																					// Propagate

	for (int i = S->nAssignments - 1; i >= 0; i--)													// Assign decided variables
	{
		int *lemma = &S->assignments[i];
		if (!S->model[S->assignments[i]] && !S->false[S->assignments[i]])
		{
			assign(S, lemma, 0);
			propagate(S);																			// Propagate
		}
	}
}

void initCDCL(struct solver *S, int nVars, int nClauses)											// Initialize the CDCL state
{
	if (nVars < 1)																					// The code assumes that there is at least one variable
		nVars = 1;

	S->nVars = nVars;																				// The number of variables
	S->nClauses = nClauses;																			// The number of clauses
	S->maxLemmas = 2000;																			// The initial maximum number of learnt clauses
	S->nLemmas = 0;																					// The number of learnt clauses -- redundant means learnt
	S->nConflicts = 0;																				// The number of conflicts which is used to updates scores
	S->nRestarts = 0;																				// The number of restarts
	S->fast = S->slow = 1 << 24;																	// The fast and slow moving averages

	S->model = getMemory(S, nVars + 1);																// Complete initial assignment (false) of the variables
	S->next = getMemory(S, nVars + 1);																// The next variable in the heuristic order
	S->prev = getMemory(S, nVars + 1);																// The previous variable in the heuristic order
	S->clauseBuffer = getMemory(S, nVars);		 													// A buffer to store a temporary clause
	S->reason = getMemory(S, nVars + 1);	 														// An array of clauses
	S->falseStack = getMemory(S, nVars + 1);														// The stack of falsified literals -- this pointer is never changed
	S->forced = S->falseStack;																		// Points to first decision (unforced literal) inside *falseStack
	S->processed = S->falseStack;		 															// Points to first unprocessed literal inside *falseStack
	S->assigned = S->falseStack;		 															// Points to last unprocessed literal inside *falseStack

	S->false = getMemory(S, 2 * nVars + 1);															// The labels for variables, non-zero means false
	S->false += nVars;
	S->first = getMemory(S, 2 * nVars + 1);															// The offset of the first watched clause
	S->first += nVars;

	int i;
	for (i = 1; i <= nVars; i++)																	// Initialize the main data structures:
	{
		S->prev[i] = i - 1;
		S->next[i - 1] = i;							  												// the double-linked list for variable-move-to-front,
		S->model[i] = S->false[-i] = S->false[i] = 0; 												// the model (phase-saving), the false array,
		S->first[i] = S->first[-i] = END;															// and first (watch pointers),
	}
	S->head = nVars;																				// the head of the double-linked list.
}

void initDB(struct solver *S)																		// Initialize the database
{
	S->DB = (int *)malloc(sizeof(int) * MEM_MAX);													// Allocate memory for the database
	S->mem_used = 0;																				// The number of integers stored in the DB
	S->DB[S->mem_used++] = 0;																		// Make sure there is a 0 before the clauses are parsed
}

int parse(struct solver *S, char *filename)															// Parse the DIMACS file and initialize the solver struct
{
	FILE *input = fopen(filename, "r");																// Open the DIMACS file for reading
	if (input == NULL)
		printf("c FILE NOT FOUND\n"), exit(ERROR);													// Exit if file was not found

	initDB(S);																						// Initialize the database

	int matchedItems;

	if (MODE == MODE_PROPAGATE || MODE == MODE_STATUS)												// Parse the additional comment lines
	{
		int i;

		do
		{
			matchedItems = fscanf(input, " c d%i", &S->nDeadVars);									// Parse number of dead (i.e. always false) variables
			if (matchedItems > 0 && matchedItems != EOF)											// Break from loop on match
				break;
			matchedItems = fscanf(input, "%*s\n");													// Skip rest of line otherwise
		}
		while (matchedItems != 1 && matchedItems != EOF);

		S->deadVars = getMemory(S, S->nDeadVars);													// Allocate memory for the list of dead variables
		i = 0;
		while (i < S->nDeadVars)																	// Parse dead variable indices
		{
			fscanf(input, "%i", &matchedItems);
			S->deadVars[i++] = -matchedItems;
		}

		fseek(input, 0, SEEK_SET);																	// Reset file position

		do
		{
			matchedItems = fscanf(input, " c v%i", &S->nAssignments);								// Parse number of variable assignments
			if (matchedItems > 0 && matchedItems != EOF)											// Break from loop on match
				break;
			matchedItems = fscanf(input, "%*s\n");													// Skip rest of line otherwise
		}
		while (matchedItems != 1 && matchedItems != EOF);

		S->assignments = getMemory(S, S->nAssignments);												// Parse variable assignments
		i = 0;
		while (i < S->nAssignments)
		{
			fscanf(input, "%i", &S->assignments[i++]);
		}

		fseek(input, 0, SEEK_SET);																	// Reset file position
	}

	do
	{
		matchedItems = fscanf(input, " p cnf %i %i \n", &S->nVars, &S->nClauses);					// Parse the first non-comment line (problem line)
		if (matchedItems > 0 && matchedItems != EOF)												// Break from loop on match
			break;
		matchedItems = fscanf(input, "%*s\n");														// Skip rest of line otherwise
	}
	while (matchedItems != 2 && matchedItems != EOF);

	initCDCL(S, S->nVars, S->nClauses);																// Initialize the CDCL state

	int nUnreadClauses = S->nClauses, clauseSize = 0;												// Initialize the number of clauses to read
	while (nUnreadClauses > 0)																		// While there are clauses in the file
	{
		int literal = 0;
		matchedItems = fscanf(input, " %i ", &literal);												// Parse a literal
		if (!literal)																				// If reached the end of the clause (denoted by a "0")
		{
			int *clause = addClause(S, S->clauseBuffer, clauseSize, 1);								// Add the clause to database

			if (!clauseSize || ((clauseSize == 1) && S->false[clause[0]]))							// Check for empty clause or conflicting unit
				return UNSAT;																		// If either is found return UNSAT

			if ((clauseSize == 1) && !S->false[-clause[0]])											// Check for a new unit
			{
				assign(S, clause, 1);																// Directly assign new units (forced = 1)
			}

			clauseSize = 0;																			// Reset buffer

			--nUnreadClauses;
		}
		else
			S->clauseBuffer[clauseSize++] = literal;												// Add literal to buffer
	}

	fclose(input);																					// Close the DIMACS file

	return SAT;																						// Return that no conflict was observed
}

int main(int argc, char **argv)																		// The main procedure
{
	if (argc == 1)
		printf("Usage: microsat [--version] [--status | --propagate] DIMACS_FILE\n"), exit(OK);		// Print usage and exit if no argument is given

	if (!strcmp(argv[1], "--version"))
		printf(VERSION "\n"), exit(OK);																// Print version and exit if argument --version is given
	else if (!strcmp(argv[1], "--status"))
		MODE = MODE_STATUS;																			// Set mode to check status of an assignment if argument --status is given
	else if (!strcmp(argv[1], "--propagate"))
		MODE = MODE_PROPAGATE;																		// Set mode to propagate an assignment if argument --propagate is given
	else
		MODE = MODE_SOLVE;																			// Default mode: SAT solving

	struct solver S;																				// Create the solver struct
	if (parse(&S, argv[argc-1]) == UNSAT)															// Parse the DIMACS file
		printf("s UNSATISFIABLE\n"), exit(UNSAT);													// Exit if the parsed problem contains a conflict even before solving

	int status;
	if (MODE == MODE_PROPAGATE || MODE == MODE_STATUS)
	{
		if (MODE == MODE_PROPAGATE)																	// Print all variable decisions implied by propagation
			propagateAssignment(&S), printImpliedDecisions(&S);

		status = checkStatus(&S);																	// Check and print problem status
		if (status == INVALID)
			printf("s INVALID\n");
		else if (status == INCOMPLETE)
			printf("s INCOMPLETE\n");
		else
			printf("s BUILDABLE\n");
	}
	else
	{
		status = solve(&S);																			// Solve without limit (number of conflicts)
		if (status == UNSAT)																		// and print whether the formula has a solution
			printf("s UNSATISFIABLE\n");
		else
			printf("s SATISFIABLE\n");
	}

	exit(status);																					// Exit with problem status code
}
