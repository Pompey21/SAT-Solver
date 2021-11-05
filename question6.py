from z3 import *
from functools import reduce
"""
    Z3 takes as input simple-sorted formulas that may contain symbols with pre-defined meanings defined by a theory.
"""
number_employees = 9
number_shifts = 21

solver = Solver()

# generating the variables
variables = []
for j in range(number_shifts):
    shifts = []
    for i in range(number_employees):
        strs = Int(f'x_{i}_{j}')
        shifts.append(strs)
    variables.append(shifts)

# set of employees
employees = range(9)
shifts = range(21)

# a) There are only 2 employees per shift
# adding variables to solver as a restricted integers (either 1 or 0)
for i in employees:
    for j in shifts:
        solver.add( Or(variables[j][i] == 0,variables[j][i] == 1) )

for j in shifts:
    score = 0
    for i in range(len(variables[j])):
        score = score + variables[j][i]
    solver.add(score == 2)


# b) no back-2-back shifts
for j in shifts:
    for i in employees:
        solver.add( Or(variables[j][i] == 0, variables[(j+1)%21][i] == 0))


# c) 
num_shifts_worker = []
for i in employees:
    num_shifts = 0
    for j in shifts:
        num_shifts = num_shifts + variables[j][i]
    num_shifts_worker.append(num_shifts)

fst_elem = num_shifts_worker[0]
for elem in num_shifts_worker:
    solver.add( fst_elem == elem )
    # solver.add( And(reduce(lambda x,y: x+y, num_shifts_worker), ))



print(solver.check())
print(solver.model())
        

print(variables)




