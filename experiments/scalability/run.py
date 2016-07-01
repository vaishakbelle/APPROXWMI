
import networkx as nx
import re,sys
import matplotlib.pyplot as plt
import itertools
from z3 import *
from vol import *
from ApproxMC import *
import os.path
from os import listdir
import random
from numpy import array,histogram,median
from scipy.stats import linregress
from copy import deepcopy
import re

'''a simple class to maintain z3 solver, latte bounds, and other variables needed for computing volume'''
class Theory: 
    def __init__(self):
        # SMT z3 solver
        self.s = Solver()
        # weights for constraints
        self.pwd = {}
        # constraints encoded in latte format 
        self.ld = {} 
        # bounds for latte variables
        self.bounds = []
        # Boolean decision variables for SMT solver, which are associated with weights and latte descriptions
        self.dvars = [] # CHANGE to latte_vars when stable  
        # Set of formulas in cnf for the SAT solver (cryptominisat)
        self.cnf_formulas = []

        # mapping from cnf ids to smt variables
        self.cnf2smt_varmap = {}

        # maps Boolean decision variable names to cnf variable indices
        self.names2ids = {}

        # mapping from names to variables
        self.variables = {}

        # list of candidate names for theory variables
        self.theoryvarlist = "uvwxyz"

        # encoder to turn boolean abstraction to cnf
        self.cnf_encoder = Then('simplify', 'tseitin-cnf')
        
        # map collecting tseitin variables in cnf encoding
        self.tseitin_vars = {}

    def load(self, filename,abstraction):

        f=open(filename)                

        for row in f:
            data=row.strip().split(",")
            bvar=data[0]
            smtformula=data[1]
            latteformula=data[2]
            weight=data[3]

            if not weight: 
                if not abstraction:
            
                    # recover bound
                    self.bounds.append(latteformula)

            elif bvar:
                # update Boolean variables
                self.update_bvars(bvar)

                # add Latte formula
                if abstraction:
                    self.ld[bvar]=""
                else:    
                    self.ld[bvar]=latteformula

                # add Latte weight
                self.pwd[bvar]=weight

                if smtformula:
                    raise Exception("ERROR: format requires variable definition to be separate from SMT formulas")

            else:
                # update Theory variables
                self.update_tvars(smtformula)

                # add Theory formula
                formula = parse_smt2_string(smtformula, decls=self.variables)
                print formula
                if abstraction: 
                    if self.get_theoryvars(smtformula): 
                        print "theory vars with abstraction, skipping %s", formula
                        continue

                self.add(formula)

                # add cnf formula
                self.add_cnf_formula(formula)
            
        f.close()

    def add(self, e):
        self.s.add(e)

    def update_bvars(self, bvar):
        if not self.variables.has_key(bvar):
            self.variables[bvar] = Bool(bvar)
            self.dvars.append(self.variables[bvar])
            cnf_id = len(self.dvars)+len(self.tseitin_vars)
            self.names2ids[bvar] = cnf_id 
            self.cnf2smt_varmap[cnf_id] = self.variables[bvar]

    def update_tvars(self, smtformula):
        for tvar in self.get_theoryvars(smtformula):
            if not self.variables.has_key(tvar):
                self.variables[tvar] = Real(tvar)

    def get_theoryvars(self, formula):     
        theoryvars = set()
        for varname in self.theoryvarlist:
            if varname in formula:
                theoryvars.add(varname)
        return theoryvars

    def save_cnf_formulas(self, filename):
        f=open(filename,"w")
        f.write('c cnf file for scalability data\n')
        f.write('p cnf %d %d\n' %(len(self.dvars)+len(self.tseitin_vars),len(self.cnf_formulas)))
        f.writelines(self.cnf_formulas)
        
    def add_cnf_formula(self, formula):
        cnf_formula = self.cnf_encoder(formula)
        assert len(cnf_formula) == 1
        cnf_formulas = []

        for term in cnf_formula[0]:

            atoms=[]

            if term.decl().kind() == 265L: # formula is something like Not(a)
                atoms.append(str(-1*self.names2ids[str(term.arg(0))]))

            elif term.decl().kind() == 262L: # formula is something like Or(b,Not(a))
                for i in range(term.num_args()): 
                    atom = term.arg(i)
                    weight = 1

                    if term.arg(i).decl().kind() == 265L:  # negated formula                       
                        assert len(term.arg(i).children()) == 1
                        atom = term.arg(i).children()[0]
                        weight = -1

                    atomstr=str(atom)

                    if self.names2ids.has_key(atomstr):                            
                        cnf_id = self.names2ids[atomstr]

                    elif re.search("[a-z]![0-9]+",atomstr): # tseitin variable
                        if not self.tseitin_vars.has_key(atomstr):
                            print "Adding tseitin variable '%s'" %atomstr
                            cnf_id = len(self.dvars)+len(self.tseitin_vars)+1
                            self.tseitin_vars[atomstr] = cnf_id
                            self.cnf2smt_varmap[cnf_id] = None # skip tseitin variable in volume estimation
                        else:
                            cnf_id = self.tseitin_vars[atomstr]
                    else:
                        print "Found non-Boolean atom '%s', skipping formula '%s'" %(atom,cnf_formula)
                        return 

                    atoms.append(str(weight * cnf_id))                

            else: # formula is a variable
                atoms.append(str(self.names2ids[str(term)]))

            cnf_formulas.append(" ".join(atoms) + " 0\n")

        self.cnf_formulas.extend(cnf_formulas)

def load_data(datadir,abstraction=False):
    
    problem_set={}
    
    if not os.path.isdir(datadir):
        raise Exception("ERROR: <%s> is not a directory" %datadir)
        
    for filename in os.listdir(datadir):
        fullname=datadir+"/"+filename
        if not os.path.isfile(fullname):
            print "Skipping non-regular file %s" %filename
            continue
        if filename.startswith("._") or filename.startswith(".D"):
            print "Skipping non-regular file %s" %filename
            continue
        prefix=filename.split(".")[0]
        t = Theory()
        print "Loading problem " + filename
        t.load(fullname,abstraction)
        problem_set[prefix] = t

    return problem_set

def solve_problem_set(problem_set,tilt,approx=True,exact=False):

    for (problem_name,theory) in problem_set.items():
        print "Solving problem " + problem_name
        print theory

        if approx:
            start_time = time.time()
            approx_vol=approximate_volume(theory,problem_name,tilt)
            end_time = time.time()
            print "APPROX volume = %f" % approx_vol
            print_problem_stats(theory)
            print "Elapsed time was " + str(end_time - start_time)      
        if exact:
            start_time = time.time()
            mc,vol=volume_mc(theory.s,theory.pwd,theory.ld,theory.bounds,theory.dvars)
            print "EXACT volume,mc = %f, %f" % (vol,mc)
            end_time = time.time()
            print "Elapsed time was " + str(end_time - start_time)     

        if approx:     
            print "DIFFERENCE exact volume=%f approx volume=%f difference(%%)=%f" %(vol,approx_vol,(vol-approx_vol)/vol)


def print_problem_stats(theory):
    print "Size of theory was " + str(len(theory.s.assertions()))
    print "Problem size was " + str(len(theory.cnf_formulas))


def check_feasibility(problem):
    t=build_boolean_theory(problem,"le")
    if t.s.check() != sat:
        return False
    t=build_boolean_theory(problem,"ge")
    if t.s.check() != sat:
        return False
    return True

def approximate_volume(t,problem_name, tilt):
    
    # variables for approx
    runIndex = str(int(time.time()))
    timeout = 2500
    initialFileName = ''
    numVariables = 0
    numClauses = 0
    pivot=0
    numIterations = 1
    leapfrogging = True
    shouldLog = False
    outputFileName = ''
    logFileName = ''
    
    # create initial dimacs CNF file
    initialFileName = "tmp/" + problem_name+'.cnf'
    t.save_cnf_formulas(initialFileName)

    # read file    
    f = open(initialFileName,'r')
    lines = f.readlines()
    f.close()
    numVariables = 0
    numClauses = 0
    for line in lines:
        if (str(line.strip()[0:5]) == 'p cnf'):
            fields = line.strip().split(' ')
            numVariables = int(fields[2])
            numClauses = int(fields[3])
            break
    initialFileNameSuffix =  initialFileName.split('/')[-1][:-4]
    finalFileName = TMPDIR+"/inputFiles/input_"+str(initialFileNameSuffix)+'_'+str(runIndex)+".cnf"
    # ApproxMC global vars
    init()

    # user-specified constants
    epsilon = .8
    delta = .2
    pivot = 2*math.ceil(4.4817*(1+1/epsilon)*(1+1/epsilon))
    numIterations = FindFromTable(1-delta)
    if (numIterations == 0):
        numIterations = int(math.ceil(35*math.log((3*1.0/delta),2)))
    
    # # exact
    # print 'Exact WMI is ' + str(volume(t.s,t.pwd,t.ld,t.bounds,t.dvars))
    # approx
    CountEstimate, wmi, wmax = ApproxWMI(runIndex, timeout, initialFileName, numVariables, numClauses, pivot, numIterations, tilt, shouldLog,logFileName,finalFileName,initialFileNameSuffix, t)
    os.system('rm '+finalFileName)
    # print results
    OutputResult(epsilon,delta, CountEstimate, wmi, wmax, outputFileName)
    print "done computing approx WMI"

    return wmi


if __name__ == "__main__":

    if len(sys.argv) < 3:
        print "Usage: " + sys.argv[0] + " <data_dir> <tilt> <abstraction>"
        sys.exit(0)

    datadir=sys.argv[1]
    tilt=int(sys.argv[2])
    abstraction = eval(sys.argv[3])

    problem_set=load_data(datadir,abstraction)      
    solve_problem_set(problem_set,tilt,approx=True,exact=True)

