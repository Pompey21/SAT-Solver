from z3 import *
from functools import reduce
"""
    Z3 takes as input simple-sorted formulas that may contain symbols with pre-defined meanings defined by a theory.
"""
# in order to play around with the model, please just change the number of employees and the number of shifts
# which are defined as integer variables here:

number_employees = 9
number_shifts = 18

solver = Solver()

# generating the variables, where each variable is defined as employee i doing shift j
# this is then stored in a variable of the form x_i_j which will be True if employee i
# is indeed taking shift j.
variables = []
for j in range(number_shifts):
    shifts = []
    for i in range(number_employees):
        strs = Int(f'x_{i}_{j}')
        shifts.append(strs)
    variables.append(shifts)

# set of employees
employees = range(number_employees)
shifts = range(number_shifts)

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
# here we check that no two consequtive variables (= denoting the shifts with j and employees with i)
# are True -> looking at consequtive shifts of the same employee!
# The wrap around case is handled by the modulo function!
for j in shifts:
    for i in employees:
        solver.add( Or(variables[j][i] == 0, variables[(j+1)%number_shifts][i] == 0))


# # c) Check that all are doing Equal Shifts
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

# for var in solver.model():
#     print(var)




