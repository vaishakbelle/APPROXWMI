# Weighted Volume Computation 
# author: Vaishak Belle 
# using Z3 version 4.3.2
# using LattE integrale 1.6
# can deal with mixtures of numeric and symbolic weights 

from z3 import *
import csv 
import sys 
import subprocess 
import time 
import re

def get_volume(buf):
    match=re.search("Decimal: ([^\n]*)\n",buf)
    if not match:
	raise Exception("Cannot parse integrate output")
    return float(match.group(1))		

'''convert (latte) fraction to float'''
def convert_to_float(frac_str):
    try:
        return float(frac_str)
    except ValueError:
        try:
            num, denom = frac_str.split('/')
            leading, num = num.split(' ')
        except ValueError:
            return float(num) / float(denom)        
        if float(leading) < 0:
            sign_mult = -1
        else:
            sign_mult = 1
        return float(leading) + sign_mult * (float(num) / float(denom))

'''a simple class to maintain z3 solver, latte bounds, and other variables needed for computing volume'''
class Theory: 
    def __init__(self):
        self.s = Solver()
        self.pwd = {}
        self.ld = {} 
        self.bounds = []
        self.dvars = []   
    
    def add(self, e):
        self.s.add(e)


'''read a dimacs model (i.e., string of variable numbers being set positive or negative)
and check for theory consistency. So, simply add these literals to a copy of this solver
and check whether it is theory consistent. Given solver, bool array and dimacs''' 

def theory_cons(s, b, model):

    # create copy 
    t = Solver()
    t.assert_exprs(s.assertions())
    
    # read dimacs model 
    for x in model.split():
        if isinstance(x, int): 
            key = int(x)
            if key > 0: 
                t.add(b[key] == True)
            else: 
                t.add(b[key] == False)
        
    return (t.check() == 'sat')

'''given a theory instance and a dimacs model (that is, propositions set to true and
false), theory consistency is checked after adding the model and volume is returned
(along with the indication whether the dimacs model was theory consistent)'''

def assert_and_getvol(t, model):

    # create copy 
    s = Solver()
    s.assert_exprs(t.s.assertions())

    # recover mapping from cnf to smt variables
    if hasattr(t,'cnf2smt_varmap'):
        varmap=t.cnf2smt_varmap
        offset=0
    else:
        varmap=t.dvars
        offset=-1
        
    # read dimacs model     
    numbers = map(int, model.split())
    for key in numbers:        
        if (key != 0): # dimacs EOF
            if varmap[abs(key)+offset] == None: # skip tseitin variables
                continue
            if key > 0:
                s.add(varmap[key+offset] == True)
                # true_variables.add(str(varmap[key+offset]))
            else: 
                s.add(varmap[abs(key)+offset] == False)
    
    #print 'current smt theory is ' +  str(s)
    if (s.check() == sat):
        return 1, volume_model(s, t.pwd, t.ld, t.bounds, t.dvars)
    else: 
        return 0, 0


'''computes weighted volume for smt model: doesnt repeatedly check for all models'''
def volume_model(s, pwd, ld, bounds, dvars):
    currentweight = 1
    dimB = 0 # dim. of B matrix
    latteoutput = []
    polyoutput = []
    polyweights = False 

    for x in dvars:
        key = str(x)
        if (s.model()[x]):
            if (is_true(s.model()[x])):
                if (ld[key]):
                    # add constraint (two-line support for intervals)
                    if (ld[key].find("|") != -1):
                        first, second = ld[key].split('|')
                        latteoutput.append(first)
                        latteoutput.append(second)
                        dimB += 2
                    else:    
                        latteoutput.append(ld[key])
                        dimB += 1
        
                if (pwd[key]):
                    # if (pwd[key].find("[") != -1):
                    #     # add polynomial
                    #     polyweights = True
                    #     polyoutput.append(pwd[key])
                    # else:
                    #     # multiply numeric weight
                    currentweight *= float(pwd[key])

    if latteoutput:    
        # add bounds 
        for bound in bounds:
            first, second = bound.split('|')
            latteoutput.append(first)
            latteoutput.append(second)
            dimB += 2

        # dimension of A matrix    
        dimA = len(latteoutput[0].replace("-","").split())

        # append latte dimensions 
        dimensions = str(dimB) + ' ' + str(dimA)
        latteoutput.append(dimensions)            
        latteoutput.reverse()

        with open('model.hrep.latte','w') as outfile: 
            outfile.writelines("%s\n" % l for l in latteoutput)
    
        if polyweights: 
            with open('model.polynomial','w') as outfile:
                outfile.writelines("[[1,[")
                outfile.writelines("%s," % l for l in polyoutput)
                outfile.writelines("]]]")

        # call latte binary  
        if polyweights:
            args = ("integrate", "--valuation=integrate", "--product-linear-forms=model.polynomial", "model.hrep.latte")
        else:    
            args = ("integrate", "--valuation=volume", "--triangulate", "model.hrep.latte")

        strout = subprocess.check_output(args)
	currentvolume = get_volume(strout)
        print 'current volume is %f' %currentvolume
        currentweight *= currentvolume 

    return currentweight

    
'''exactly like volume(...), but also returns model count'''

def volume_mc(s, pwd, ld, bounds, dvars):

     # total model count number
    count = 0 
    # print "assertions"
    # print s.assertions()

    # total model weight 
    modelweight = 0 
    # print s
    # print dvars

    while s.check() == sat:

        #print "curr model" 
        #print s.model() 
                
        currentweight = 1.0
        dimB = 0 # dim. of B matrix
        latteoutput = []
        polyoutput = []
        polyweights = False 
            
        # iterating over an array of Bools    
        # for x in s.model(): 
        #     for y in s.model()[x].as_list():
        #         print y

        for x in dvars:
            key = str(x)
            if (s.model()[x]):
                if (is_true(s.model()[x])):
                    if (ld[key]):
                        # add constraint (two-line support for intervals)
                        if (ld[key].find("|") != -1):
                            first, second = ld[key].split('|')
                            latteoutput.append(first)
                            latteoutput.append(second)
                            dimB += 2
                        else:    
                            latteoutput.append(ld[key])
                            dimB += 1
                    
                    if (pwd[key]):
                        # if (pwd[key].find("[") != -1):
                        #     # add polynomial
                        #     polyweights = True
                        #     polyoutput.append(pwd[key])
                        # else:
                            # multiply numeric weight 
                        currentweight *= float(pwd[key])
            
        if latteoutput:    

            # add bounds 
            for bound in bounds:
                first, second = bound.split('|')
                latteoutput.append(first)
                latteoutput.append(second)
                dimB += 2

            # dimension of A matrix    
            dimA = len(latteoutput[0].replace("-","").split())
            
            # append latte dimensions 
            dimensions = str(dimB) + ' ' + str(dimA)
            latteoutput.append(dimensions)            
            latteoutput.reverse()
        
            with open('model.hrep.latte','w') as outfile: 
                outfile.writelines("%s\n" % l for l in latteoutput)
                
            if polyweights: 
                with open('model.polynomial','w') as outfile:
                    outfile.writelines("[[1,[")
                    outfile.writelines("%s," % l for l in polyoutput)
                    outfile.writelines("]]]")
        
            # call latte binary  
            if polyweights:
                args = ("integrate", "--valuation=integrate", "--product-linear-forms=model.polynomial", "model.hrep.latte")
            else:    
                args = ("integrate", "--valuation=volume", "--triangulate", "model.hrep.latte")
           

            strout = subprocess.check_output(args)
            currentvolume = get_volume(strout)
            print 'current volume is %f' %currentvolume
            currentweight *= currentvolume
       
        modelweight += currentweight

        # discard model 
        G = False
        # print dvars
        for x in dvars:
            if (s.model()[x]):
                G = Or(G, x != s.model()[x])
            else: 
                G =Or(G,x == True)

        # increment model count         
        count += 1
        s.add(G)


    return count, modelweight     
    
'''exactly like volume_mc(...), except that model couning quits on pivot ratio'''

def bounded_wmi(s, pwd, ld, bounds, dvars, pivot, tilt, wmax, wmin):

     # total model count number
    count = 0 
    # total model weight 
    modelweight = 0 

    while s.check() == sat:

        print "curr model" 
        print s.model() 
                
        currentweight = 1.0
        dimB = 0 # dim. of B matrix
        latteoutput = []
        polyoutput = []
        polyweights = False 
            
        # iterating over an array of Bools    
        # for x in s.model(): 
        #     for y in s.model()[x].as_list():
        #         print y

        for x in dvars:
            key = str(x)
            if (s.model()[x]):
                if (is_true(s.model()[x])):
                    if (ld[key]):
                        # add constraint (two-line support for intervals)
                        if (ld[key].find("|") != -1):
                            first, second = ld[key].split('|')
                            latteoutput.append(first)
                            latteoutput.append(second)
                            dimB += 2
                        else:    
                            latteoutput.append(ld[key])
                            dimB += 1
                    
                    if (pwd[key]):
                        # if (pwd[key].find("[") != -1):
                        #     # add polynomial
                        #     polyweights = True
                        #     polyoutput.append(pwd[key])
                        # else:
                            # multiply numeric weight 
                        currentweight *= float(pwd[key])
            
        if latteoutput:    

            # add bounds 
            for bound in bounds:
                first, second = bound.split('|')
                latteoutput.append(first)
                latteoutput.append(second)
                dimB += 2

            # dimension of A matrix    
            dimA = len(latteoutput[0].replace("-","").split())
            
            # append latte dimensions 
            dimensions = str(dimB) + ' ' + str(dimA)
            latteoutput.append(dimensions)            
            latteoutput.reverse()
        
            with open('model.hrep.latte','w') as outfile: 
                outfile.writelines("%s\n" % l for l in latteoutput)
                
            if polyweights: 
                with open('model.polynomial','w') as outfile:
                    outfile.writelines("[[1,[")
                    outfile.writelines("%s," % l for l in polyoutput)
                    outfile.writelines("]]]")
        
            # call latte binary  
            if polyweights:
                args = ("integrate", "--valuation=integrate", "--product-linear-forms=model.polynomial", "model.hrep.latte")
            else:    
                args = ("integrate", "--valuation=volume", "--triangulate", "model.hrep.latte")
           
            strout = subprocess.check_output(args)
            currentvolume = get_volume(strout)
            print 'current volume is %f' %currentvolume
            currentweight *= currentvolume
       
        modelweight += currentweight

        if (currentweight !=0): 
            wmin = min(wmin, currentweight)

        # increment model count         
        count += 1

        if (modelweight / (wmin*tilt)) > pivot: 
            break 

        # discard model 
        G = False
        # print dvars
        for x in dvars:
            if (s.model()[x]):
                G = Or(G, x != s.model()[x])
            else: 
                G =Or(G,x == True)

        s.add(G)


    return count, modelweight, wmin         

'''Computes weighted volume for a SMT theory: given solver instantiated with the sentences of the theory,
 weight and latte dictionaries, and latte bounds.'''

def volume(s, pwd, ld, bounds, dvars):

    # total model weight 
    modelweight = 0 
    
    while s.check() == sat:

        print s.model() 
                
        currentweight = 1.0
        dimB = 0 # dim. of B matrix
        latteoutput = []
        polyoutput = []
        polyweights = False 
            
        # iterating over an array of Bools    
        # for x in s.model(): 
        #     for y in s.model()[x].as_list():
        #         print y

        for x in dvars:
            key = str(x)
            if (s.model()[x]):
                if (is_true(s.model()[x])):
                    if (ld[key]):
                        # add constraint (two-line support for intervals)
                        if (ld[key].find("|") != -1):
                            first, second = ld[key].split('|')
                            latteoutput.append(first)
                            latteoutput.append(second)
                            dimB += 2
                        else:    
                            latteoutput.append(ld[key])
                            dimB += 1
                    
                    if (pwd[key]):
                        # if (pwd[key].find("[") != -1):
                        #     # add polynomial
                        #     polyweights = True
                        #     polyoutput.append(pwd[key])
                        # else:
                            # multiply numeric weight 
                        currentweight *= float(pwd[key])
            
        if latteoutput:    

            # add bounds 
            for bound in bounds:
                first, second = bound.split('|')
                latteoutput.append(first)
                latteoutput.append(second)
                dimB += 2

            # dimension of A matrix    
            dimA = len(latteoutput[0].replace("-","").split())
            
            # append latte dimensions 
            dimensions = str(dimB) + ' ' + str(dimA)
            latteoutput.append(dimensions)            
            latteoutput.reverse()
        
            with open('model.hrep.latte','w') as outfile: 
                outfile.writelines("%s\n" % l for l in latteoutput)
                
            if polyweights: 
                with open('model.polynomial','w') as outfile:
                    outfile.writelines("[[1,[")
                    outfile.writelines("%s," % l for l in polyoutput)
                    outfile.writelines("]]]")
        
            # call latte binary  
            if polyweights:
                args = ("integrate", "--valuation=integrate", "--product-linear-forms=model.polynomial", "model.hrep.latte")
            else:    
                args = ("integrate", "--valuation=volume", "--triangulate", "model.hrep.latte")
            
            strout = subprocess.check_output(args)
	    currentvolume = get_volume(strout)
            print 'current volume is %f' %currentvolume
            currentweight *= currentvolume 
        
        modelweight += currentweight

        # discard model 
        G = False
        # print dvars
        for x in dvars:
            if (s.model()[x]):
                G = Or(G, x != s.model()[x])
            else: 
                G =Or(G,x == True)

        s.add(G)            

    return modelweight 

''' read from data.csv'''
def csv_theory():
    
    x, y, z, u, v, w = Ints('x y z u v w')
    a, b, c, d, e, f, g, h, p,q,r,i,j = Bools('a b c d e f g h p q r i j')
    a1, a2, b1, b2, c1, c2, d1, d2, e1, e2, f1, f2, f3, f4, f5, f6, f7, f8, f9 = Bools('a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 f1 f2 f3 f4 f5 f6 f7 f8 f9')
    a3, a4, a5, b3, b4, b5, c3, c4, c5, d3, d4, d5, e3, e4, e5, ap, bp, cp, dp, ep, aq, bq, cq, dq, eq, ar, br, cr, dr, er, bs, cs, ds, es, at, bt, ct, dt, et = Bools('a3 a4 a5 b3 b4 b5 c3 c4 c5 d3 d4 d5 e3 e4 e5 ap bp cp dp ep aq bq cq dq eq ar br cr dr er bs cs ds es at bt ct dt et')
    
    na1, na2, nb1, nb2, nc1, nc2, nd1, nd2, ne1, ne2, nf1, nf2, nf3, nf4, nf5, nf6, nf7, nf8, nf9 = Bools('na1 na2 nb1 nb2 nc1 nc2 nd1 nd2 ne1 ne2 nf1 nf2 nf3 nf4 nf5 nf6 nf7 nf8 nf9')
    t = Theory()
    t.bounds.append("0 1 0 0 0 0|10 -1 0 0 0 0") # x in [0, 10]
    t.bounds.append("0 0 1 0 0 0|10 0 -1 0 0 0") # y in [0, 10]
    t.bounds.append("0 0 0 1 0 0|10 0 0 -1 0 0") # z
    t.bounds.append("0 0 0 0 1 0|10 0 0 0 -1 0") # u
    t.bounds.append("0 0 0 0 0 1|10 0 0 0 0 -1") # v

    descriptions = {'p': p, 'q': q, 'r': r, 'h':h, 'i':i,'j':j, 'a' : a, 'b' : b, 'c' : c, 'd' : d, 'e': e, 'f' : f, 'a1' : a1, 'b1' : b1, 'c1' : c1, 'd1' : d1, 'e1' : e1, 'f1' : f1, 'a2' : a2, 'b2' : b2, 'c2' : c2, 'd2' : d2, 'e2' : e2, 'f2' : f2, 'a3' : a3, 'b3' : b3, 'c3' : c3, 'd3' : d3, 'e3' : e3, 'f3' : f3, 'f4': f4, 'x' :x, 'y': y, 'ap' : ap, 'bp' : bp, 'cp' : cp, 'dp' : dp, 'ep' : ep,'aq' : aq, 'bq' : bq, 'cq' : cq, 'dq' : dq, 'z': z, 'ar' : ar, 'br' : br, 'cr' : cr, 'dr' : dr, 'er' : er,  'bs' : bs, 'cs' : cs, 'ds' : ds, 'es' : es, 'u': u, 'at' : at, 'bt' : bt, 'ct' : ct, 'dt' : dt, 'et' : er, 'na1':na1, 'na2':na2, 'nb1':nb1, 'nb2':nb2, 'nc1':nb2, 'nc2':nc2, 'nd1':nd1, 'nd2':nd2, 'ne1':ne1, 'ne2':ne2, 'nf1':nf1, 'nf2':nf2, 'nf3':nf3, 'nf4':nf4, 'nf5':nf5, 'nf6':nf6, 'nf7':nf7, 'nf8':nf8, 'nf9':nf9, 'v':v}

    # data.csv format: (a) variables; (b) smt expression; (c) latte expressions, in standard form of linear inequalities, e.g. Ax <= B, so x>=1 is modeled as -x <= 1; and (d) weights (-1 for complex formulas)
    with open("data.csv") as infile:
        reader = csv.reader(infile)

        for row in reader: 

            var = row[0]
            weight = row[3]
            latte = row[2]

            t.add(parse_smt2_string(row[1],decls=descriptions))
        
            # instantiate dictionaries 
            if var:
                t.pwd[var] = float(weight) 
                t.ld[var] = latte
                t.dvars.append(eval(var))
            
        infile.close()

    # print "dvars"    
    # print t.dvars
    return t   
 

''' a simple theory for quinn.cnf'''
def quinn_theory():
    # set up WMI      
    x, y, z, u, v, w = Ints('x y z u v w')
    a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16 = Bools('a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16') 
    
    # create theory instance 
    t = Theory()
    t.bounds.append("0 1 0|12 -1 0") # x in [0, 12]
    t.bounds.append("0 0 1|8 0 -1") # y in [0, 8]
    
    A = And(x>=4,x<=6)
    t.add(a1 == A)
    B = (x<=3)
    t.add(a2 == B)
    C = And(y>=4,y<=6)
    t.add(a3 == C)
    D = (y<=3)
    t.add(a4 == D)
    t.dvars = [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16] 

    # Add formulas to SMT solver
    t.add(Or(a1, a2))
    t.add(Or(Not(a2), Not(a4)))
    t.add(Or(a3 , a4)) 
    t.add(Not(a1))   
    t.add(a5)
    t.add(Or(a5 , Not(a6)))
    t.add(Or(a6 , Not(a7)))
    t.add(Or(a6 , a7))
    t.add(Or(a7 , Not(a16)))
    t.add(Or(a8 , Not(a9)))
    t.add(Or(Not(a8) , Not(a14)))
    t.add(Or(a9 , a10))
    t.add(Or(a9 , Not(a10)))
    t.add(Or(Not(a10) , Not(a11)))
    t.add(Or(a10 , a12))
    t.add(Or(a11 , a12))
    t.add(Or(a13 , a14))
    t.add(Or(a14 , Not(a15)))
    t.add(Or(a15 , a16))
    
    # latte constraints for atoms
    t.ld["a1"] = "-4 1 0|6 -1 0"
    t.ld["a2"] = "3 1 0"
    t.ld["a3"] = "-4 0 1|6 0 -1"
    t.ld["a4"] = "3 0 1"
    t.ld["a5"] = ""
    t.ld["a6"] = ""
    t.ld["a7"] = ""
    t.ld["a8"] = ""
    t.ld["a9"] = ""
    t.ld["a10"] = ""
    t.ld["a11"] = ""
    t.ld["a12"] = ""
    t.ld["a13"] = ""
    t.ld["a14"] = ""
    t.ld["a15"] = ""
    t.ld["a16"] = ""

    # weights of atoms 
    t.pwd["a1"] = "[.2,[1,0]]" #2x 
    t.pwd["a2"] = "[.1,[1,0]]" #x
    t.pwd["a3"] = "[.2,[0,1]]" #2y 
    t.pwd["a4"] = "[.1,[0,1]]" #y 
    t.pwd["a5"] = ".3"
    t.pwd["a6"] = ".4"
    t.pwd["a7"] = ".2"
    t.pwd["a8"] = ".3"
    t.pwd["a9"] = ".5"
    t.pwd["a10"] = ".6"
    t.pwd["a11"] = ".2"
    t.pwd["a12"] = ".4"
    t.pwd["a13"] = ".5"
    t.pwd["a14"] = ".6"
    t.pwd["a15"] = ".7"
    t.pwd["a16"] = ".9"
    
    return t
    

def vol_test():
    # initalize Boolean decision variables (that is, features) 
    x, y, z, u, v, w = Ints('x y z u v w')
    a, b, c, d, e, f = Bools('a b c d e f')
 
 
    # set bounds of variables to latte (like hard constraints): here 0<=x<=12
    lattebounds = []
    lattebounds.append("0 1|12 -1")
    
    # initialize latte for variables
    latte = {}
    pwd = {}
    b == And(x>=4,x<=5)
    c == Or(a,x<=4)
    # Boolean decision variables for SMT solver
    dvars = [a, b, c]
    # Formulas for SMT solver
    X = Xor(b,c)
    # latte constraints for atoms
    latte["a"] = ""
    latte["b"] = "-4 1|6 -1"
    latte["c"] = "4 -1"
    # weights of atoms (set to 1 for unweighted volume)
    pwd["a"] = "2"
    pwd["b"] = "[2,[6]]"
    pwd["c"] = "[3,[9]]"
    
    s = Solver() 
    s.add(X)
    print 'Volume is ' + str(volume(s,pwd,latte,lattebounds,dvars))


# testing the capability to read dimacs input
def dimacs_test():
    
    s = Solver()
    
    a = Array('a', IntSort(), BoolSort())
    x, y, z, u, v, w = Ints('x y z u v w')
    b, c, d, e, f, g = Bools('b c d e f g')
    F = (x>=4) and (x<=5)
    G = b or (x<=4)
    s.add(a[0] == F)
    s.add(a[1] == G)
    X = Xor(a[0],a[1])
    s.add(X)
    # s.add(a[0]==True,a[1]==True)
    print s.check()
    print s.model()
    
    # testing solver copying
    # t = Solver()
    # t.assert_exprs(s.assertions())
    # print t
    # t.reset()
    # print t
    # print s
    
    # print theory_cons(s, a, '0 1')


# dimacs_test()


def main():


    t = csv_theory()
    start_time = time.time()
    print 'Exact (MC, WMI) is ' + str(volume_mc(t.s,t.pwd,t.ld,t.bounds,t.dvars))
    end_time = time.time()
    print("Elapsed time was %g seconds" % (end_time - start_time))

#main()
