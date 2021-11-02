import argparse
import subprocess

# turning pigeon i sitting in hole j (out of m holes) into a variable
def pigeon_hole_generator(m,i,j):
    pigeon_hole = i * m + j + 1
    return pigeon_hole

# generating the first formula
def generate_formula1(n,m):
    lst_pigeons_in_holes = []
    for i in range(0,n):
        clauses = []
        for j in range(0,m):
            pigeon_hole_var = pigeon_hole_generator(m,i,j)
            clauses.append(pigeon_hole_var)
        clauses.append(0)
        clause_str = " ".join([str(num) for num in clauses])
        lst_pigeons_in_holes.append(clause_str)
    return len(lst_pigeons_in_holes),"\n".join(lst_pigeons_in_holes)

def formula_to_string(lst_pigeons_in_holes):
    clauses = " ".join([str(pg_hl) for pg_hl in lst_pigeons_in_holes])
    return clauses

# generating the second formula
def generate_formula2(n,m):
    returning_val = []
    for h in range(m):
        for p1 in range(n):
            for p2 in range(n):
                if p1 == p2:
                    continue
                returning_val.append(" ".join([str(-pigeon_hole_generator(m,p1,h)),
                                str(-pigeon_hole_generator(m,p2,h)),
                                str(0)]))
    return len(returning_val),"\n".join(returning_val)

# generating the cnf file
def generate_cnf_file(n,m,filename):
    num_clauses_1,lst_pigeons_in_holes = generate_formula1(n,m)
    num_clauses_2,formula_2 = generate_formula2(n,m)
    nm = n*m
    num_clauses = num_clauses_1+num_clauses_2
    output = open(filename, "w+")
    output.write("c number of pigeons = "+str(n)+" ; number of holes = " + str(m))
    output.write('\n')
    output.write("p cnf " + str(nm) + " " + str(num_clauses) + "\n")
    output.write(lst_pigeons_in_holes)
    output.write('\n')
    output.write(formula_2)



def main(n,m,filename):
    generate_cnf_file(n,m,filename)


def automator():
    command = "~/MiniSat_v1.14_linux " 
    string_commants = []
    n_max = 15
    for n in range(4,n_max+1):
        filename = "output-"+str(n)+".cnf"
        string_commants.append(command + filename)
        generate_cnf_file(n,n-1,filename)
    return string_commants

string_commants = automator()


for string_commant in string_commants:
    subprocess.run(string_commant, shell=True)

