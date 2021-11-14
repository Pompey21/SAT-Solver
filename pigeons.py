#! /usr/bin/python

#################################################################################
#                                                                               #
# Formal Verification Coursework 2                                              #
#                                                                               #
# Skeleton code with examples for pigeon problem                                #
#                                                                               #
# This uses the python dd package by Ioannis Filippidis (johnyf on GitHub).     #
#                                                                               #
# Adapted from code written by Pramod Subramanyan                               #
#  (loosely based on Perl code by Bryan Brady)                                  #
#                                                                               #
#################################################################################

from dd import autoref as _bdd
import argparse
import itertools

def example1(pdfname, n):
    print ('  [Example 1]: Creating BDDs that involve simple propositional operators.')

    # Create a BDD manager. We only need one.
    bdd = _bdd.BDD()
    # Create variables x and y.
    bdd.declare('x', 'y')
    # Get pointers to these variables.
    x = bdd.var('x')
    y = bdd.var('y')
    # Compute the BDD for their disjunction: (x \/ y)
    z = x | y
    # Compute their conjunction: (x /\ y) 
    w = x & y
    # Now prove that (x /\ y) ==> (x \/ y)
    f = w.implies(z)
    if (f == bdd.true):
        print ('  - (x /\ y) ==> (x \/ y)')
    else:
        print ('  - Uh oh! We should never get here.')
    # But the converse is not true.
    g = z.implies(w)
    if (g != bdd.true):
        print ('  - But the converse is not true.')
    else:
        print ('  - Uh oh! Should never get here.')

    bdd.collect_garbage()
    bdd.dump(pdfname)

def example2(pdfname, n):
    print ('  [Example 2]: Create a BDD for an %d-bit less than expression.' % n)

    # Create a BDD manager. We only need one.
    bdd = _bdd.BDD()
    # Create variables xs and ys.
    for i in range(n):
        bdd.declare('x%d' % i)
        bdd.declare('y%d' % i)
    # Arrays with variable names.
    xs_names = ['x%d' % i for i in range(n)]
    ys_names = ['y%d' % i for i in range(n)]
    # Get references to these variables. 
    xs = [bdd.var(xs_names_i) for xs_names_i in xs_names]
    ys = [bdd.var(ys_names_i) for ys_names_i in ys_names]

    # Construct lt and ge expressions.
    lt = nBitLT(xs, ys)
    ge = nBitGE(xs, ys)

    # These two should be the negation of each other (i.e. mutually exclusive)
    miter = (lt & ~ge) | (~lt & ge)
    # Check if miter is true.
    if miter == bdd.true:
        print ('  - nBitLT and nBitGE definitions seem correct.')
    else:
        print ('  - Uh oh! We should not get here.')

    # Now let's try enumerating the assignments to lt.
    print ('  - Enumerating assignments to less-than:')
    strs = []
    for m in bdd.pick_iter(lt):
        x_str = assignmentToBinary(m,  xs_names)
        y_str = assignmentToBinary(m,  ys_names)
        strs += ['%s < %s' % (x_str, y_str)]
    strs.sort()
    for s in strs: print ('    -- %s' % s)
    # We expect strs to have 1 + 2 + ... K = K*(K+1) / 2 assignments where K = 2**n - 1
    K = 2**n - 1
    assert len(strs) == ((K * (K+1)) // 2)

def assignmentToBinary(m, vs):
    return ''.join(str(int(m[vi])) for vi in vs)

def nBitLT(xs, ys):
    """Create a less-than expression for the n-bit vector of variables in xs
    and ys.

    xs and ys should be the same length. xs[0] and ys[0] are the most
    significant bits (MSBs)."""

    assert (len(xs) == len(ys))
    # We will use recursion to compute the less-than expression.
    # 
    # The recurrence we use is as follows:
    # a[n:0] < b[n:0] == a[n] < b[n] \/ (a[n] = b[n] /\ a[n-1:0] < a[n-1:0])
    #
    # Also note: 
    #   - a[i] < b[i] == ~a[i] /\ b[i]
    #   - a[i] = b[i] == (a[i] /\ b[i]) \/ (~a[i] /\ ~b[i])
    this_bit_lt = (~xs[0]) & (ys[0])
    if len(xs) == 1:
        return this_bit_lt
    else:
        this_bit_eq = (xs[0] & ys[0]) | (~xs[0] & ~ys[0])
        return this_bit_lt | (this_bit_eq & nBitLT(xs[1:], ys[1:]))

def nBitGE(xs, ys):
    """Create a greter-than-equal expression for the n-bit vector of variables
    in xs and ys.

    xs and ys should be the same length. xs[0] and ys[0] are the most
    significant bits (MSBs)."""

    assert (len(xs) == len(ys))
    # We will use recursion to compute the greater-than-equal expression.
    # 
    # The recurrence we use is as follows:
    # a[n:0] >= b[n:0] == a[n] > b[n] \/ (a[n] = b[n] /\ a[n-1:0] >= a[n-1:0])
    #
    # Also note: 
    #   - a[i] > b[i] == a[i] /\ ~b[i]
    #   - a[i] >= b[i] == a[i] \/ ~b[i])
    #   - a[i] = b[i] == (a[i] /\ b[i]) \/ (~a[i] /\ ~b[i])
    if len(xs) == 1:
        this_bit_ge = xs[0] | ~ys[0]
        return this_bit_ge
    else:
        this_bit_gt = xs[0] & ~ys[0]
        this_bit_eq = (xs[0] & ys[0]) | (~xs[0] & ~ys[0])
        return this_bit_gt | (this_bit_eq & nBitGE(xs[1:], ys[1:]))

# ======================================================================================

"""
    FORMULA 1: Every pigeon sits somewhere
"""
def generate_list_clauses_formula_1(n):
    lst_clauses = []
    for pigeon in range(0,n):
        clause = []
        for hole in range(0,n-1):
            clause.append((pigeon,hole))
        lst_clauses.append(clause)
    return lst_clauses
            
def bdd_clauses_1_formula_1(lst_clauses,bdd,ph_2_bdd):
    lst_bdd_clauses = []

    for clause in lst_clauses:
        bdd_clause = bdd.apply('or',ph_2_bdd[clause[0]],ph_2_bdd[clause[1]])
        lst_bdd_clauses.append(bdd_clause)
        # print(bdd_clause.to_expr())
    return lst_bdd_clauses, bdd

    # for clause in lst_clauses:
    #     bdd_clause = bdd.apply('or',ph_2_bdd[clause[0]],ph_2_bdd[clause[0]])
    #     for pig_hole in clause:
    #         bdd_clause = bdd.apply('or',bdd_clause,ph_2_bdd[pig_hole])
    #         # print(bdd_clause.to_expr())
    #     lst_bdd_clauses.append(bdd_clause)
    # return lst_bdd_clauses, bdd

def bdd_clauses_2_formula_1(lst_bdd_clauses,bdd,ph_2_bdd):
    bdd_clause = lst_bdd_clauses[0]
    for clause in lst_bdd_clauses:
        bdd_clause = bdd.apply('and',bdd_clause,clause)
    return bdd_clause, bdd


"""
    FORMULA 2: Every pigeon sits somewhere
"""
def generate_list_clauses_formula_2(n):
    pigeons = list(range(n))
    combinations_pigeons = list(itertools.combinations(pigeons, 2))
    lst_clauses = []
    for hole in range(0,n-1):
        for pair in combinations_pigeons:
            clause = [(pair[0],hole) , (pair[1],hole)]
            lst_clauses.append(clause)
    return lst_clauses

def bdd_clauses_1_formula_2(lst_clauses,bdd,ph_2_bdd):
    lst_bdd_clauses = []
    for clause in lst_clauses:
        bdd_clause = bdd.apply('or',~ph_2_bdd[clause[0]],~ph_2_bdd[clause[1]])
        lst_bdd_clauses.append(bdd_clause)
        # print(bdd_clause.to_expr())
    return lst_bdd_clauses, bdd

def bdd_clauses_2_formula_2(lst_bdd_clauses,bdd,ph_2_bdd):
    bdd_clause = lst_bdd_clauses[0]
    for clause in lst_bdd_clauses:
        bdd_clause = bdd.apply('and',bdd_clause,clause)
    return bdd_clause, bdd



def pigeonhole(pdfname, n):
    # Create a BDD manager. We only need one.
    ph_2_bdd = {}
    bdd = _bdd.BDD()
    for p1 in range(n):
        for h in range(n-1):
            pigeon_hole = f"x_{p1}_{h}"
            bdd.declare(pigeon_hole)
            ph_2_bdd[(p1,h)] = bdd.var(pigeon_hole)

    """FORMULA 1"""
    lst_clauses_form_1 = generate_list_clauses_formula_1(n)
    print('List of clauses: ')
    print(lst_clauses_form_1)
    print('******')
    lst_bdd_clauses_form_1,bdd = bdd_clauses_1_formula_1(lst_clauses_form_1,bdd,ph_2_bdd)
    bdd_clause_form_1,bdd = bdd_clauses_2_formula_1(lst_bdd_clauses_form_1,bdd,ph_2_bdd)
    print(bdd.to_expr(bdd_clause_form_1))

    """FORMULA 2"""
    lst_clauses_form_2 = generate_list_clauses_formula_2(n)
    print('List of clauses: ')
    print(lst_clauses_form_2)
    print('******')
    lst_bdd_clauses_form_2,bdd = bdd_clauses_1_formula_2(lst_clauses_form_2,bdd,ph_2_bdd)
    bdd_clause_form_2,bdd = bdd_clauses_2_formula_2(lst_bdd_clauses_form_2,bdd,ph_2_bdd)
    print(bdd.to_expr(bdd_clause_form_2))

    # print(bdd.to_expr())

    bdd.collect_garbage()
    bdd.dump(pdfname)



    

# <><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
# ======================================================================================

def main():
    # List of examples.
    examples = [example1, example2, pigeonhole]
    # Argument parsing.
    parser = argparse.ArgumentParser()
    example_choices = [x+1 for x in range(len(examples))]
    example_help_message = 'Example to run (1-%d). Default=1.' % len(examples)
    parser.add_argument("--example", type=int, help=example_help_message, default=1, choices=example_choices)
    parser.add_argument("--n", type=int, help='Value of n (default=2). (Only for examples 2 and 3.)', default=2)
    parser.add_argument("--pdf", type=str, help='PDF image output filename (Only for example 1.)', default='bdd.pdf')
    args = parser.parse_args()

    # Print a header.
    print ('** FV assignment **\n')
    
    # Run the example.
    ex_to_run = examples[args.example - 1]
    ex_to_run(args.pdf, args.n)

    # Pigeon Hole System
    pigeonhole('3pigeons.pdf',3)

if __name__ == '__main__':
    main()

