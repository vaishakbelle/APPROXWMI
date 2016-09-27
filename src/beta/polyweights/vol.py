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




    
'''returns volume, model count'''

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
                        if (pwd[key].find("[") != -1):
                            # add polynomial
                            polyweights = True
                            polyoutput.append(pwd[key])
                        else:
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
            
            popen = subprocess.Popen(args, stdout=subprocess.PIPE)
            popen.wait()

            # extract answer from latte output
            grepargs = ("grep", "Answer")
            answer = subprocess.Popen(grepargs, stdin=popen.stdout, stdout=subprocess.PIPE)
            popen.stdout.close()
            output = answer.stdout.read()
            currentvolume = output.replace("Answer:","").strip('\n')
            print 'current volume is ' + currentvolume
            currentweight *= convert_to_float(currentvolume)
        
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
                        if (pwd[key].find("[") != -1):
                            # add polynomial
                            polyweights = True
                            polyoutput.append(pwd[key])
                        else:
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
            
            popen = subprocess.Popen(args, stdout=subprocess.PIPE)
            popen.wait()

            # extract answer from latte output
            grepargs = ("grep", "Answer")
            answer = subprocess.Popen(grepargs, stdin=popen.stdout, stdout=subprocess.PIPE)
            popen.stdout.close()
            output = answer.stdout.read()
            currentvolume = output.replace("Answer:","").strip('\n')
            print 'current volume is ' + currentvolume
            currentweight *= convert_to_float(currentvolume)
        
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
                t.pwd[var] = weight
                t.ld[var] = latte
                t.dvars.append(eval(var))
            
        infile.close()

    # print "dvars"    
    # print t.dvars
    return t   
 




def main():


    t = csv_theory()
    start_time = time.time()
    print 'Exact (MC, WMI) is ' + str(volume_mc(t.s,t.pwd,t.ld,t.bounds,t.dvars))
    end_time = time.time()
    print("Elapsed time was %g seconds" % (end_time - start_time))

main()
