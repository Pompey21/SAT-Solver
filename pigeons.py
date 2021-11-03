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
# <><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
# turning pigeon i sitting in hole j (out of m holes) into a variable
def pigeon_hole_generator(m,i,j):
    pigeon_hole = i * m + j + 1
    return pigeon_hole

def generate_formula1(n,ph_2_bdd,bdd):
    lst_pigeons_in_holes = []
    for p1 in range(0,n):
        clause = ph_2_bdd[(p1,0)]
        for h in range(0,n-1):
            print('h = {}'.format(h))
            print('p1 = {}'.format(p1))
            if clause == ph_2_bdd[(p1,0)]:
                clause = ph_2_bdd[(p1,h)]
                # lst_pigeons_in_holes.append(clause)
            else:
                print('yes')
                clause = bdd.apply('or',clause,ph_2_bdd[(p1,h)])
                # lst_pigeons_in_holes.append(('or',bdd.to_expr(clause),'x_'+str(p1)+'_'+str(h)))
        lst_pigeons_in_holes.append(clause)
        
    all_clauses = lst_pigeons_in_holes[0] 
    for clause in lst_pigeons_in_holes:
        all_clauses = bdd.apply('and',all_clauses,clause)
    print('********')
    print(bdd.to_expr(all_clauses))
    return lst_pigeons_in_holes, bdd
            


def generate_formula2(n):
    # Create a BDD manager. We only need one.
    returning_val = []
    # we have n-1 holes!
    for h in range(n-1):
        # pigeons:)
        for p1 in range(n):
            for p2 in range(n):
                if p1 == p2:
                    continue
                returning_val.append([ph_2_bdd[(p1,h)],
                                ph_2_bdd[(p2,h)]])
    return returning_val


def pigeonhole(pdfname, n):
    # Create a BDD manager. We only need one.
    ph_2_bdd = {}
    bdd = _bdd.BDD()
    for p1 in range(n):
        for h in range(n-1):
            pigeon_hole = "x_"+str(p1)+"_"+str(h)
            bdd.declare(pigeon_hole)
            ph_2_bdd[(p1,h)] = bdd.var(pigeon_hole)
    lst_clauses, bdd = generate_formula1(n,ph_2_bdd,bdd)
    bdd.dump('test.pdf')
    print(lst_clauses)


    

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
    pigeonhole('test.pdf',3)

if __name__ == '__main__':
    main()

