
import networkx as nx
import re,sys
import matplotlib.pyplot as plt
import itertools
from z3 import *
from vol import *
from ApproxMC import *
import os.path
import random
from numpy import array,histogram,median
from scipy.stats import linregress
from copy import deepcopy

def load_data(filename):
    f=open(filename)
    header=f.readline()
    data=[row.split(',') for row in f]
    return header,data

def build_graph(links):
    g=nx.DiGraph()
    for link in links:
        m=re.match(".* between (.*) and (.*) \((.*)\)",link)
        if not m:
            print "ERROR: unmatched link '" + link + "', exiting.."
            sys.exit(0)
        #print "adding edge: ",m.groups() 
        g.add_edge(m.groups()[0].replace(' ','_'),m.groups()[1].replace(' ','_'),label=m.groups()[2])
    return g

def draw_graph(g,title="",filename="",selected_nodes=None):
    
    pos = nx.spring_layout(g)
    nx.draw_networkx(g, pos)
    if selected_nodes:
        nx.draw_networkx_nodes(g,pos,selected_nodes,node_color='g')          
    if title:
        plt.title(title)
    if filename:
        plt.savefig(filename)
    else:
        plt.show()

def fit_piecewise_linear_dist(values):
    hist,bins=histogram(values,100)    
    bin_centers=[(bins[i+1]+bins[i])/2. for i in range(len(bins)-1)]
    median_=median(values)
    for i in range(len(bin_centers)):
        if bin_centers[i] > median_:
            median_bin=i
            break
    le_median_out=array(hist[:median_bin])
    le_median_in=array(bin_centers[:median_bin])
    gt_median_out=array(hist[median_bin:])
    gt_median_in=array(bin_centers[median_bin:])
    le_params=linregress(le_median_in,le_median_out)
    gt_params=linregress(gt_median_in,gt_median_out)
    return le_params[:2],gt_params[:2]

def build_neighbourhood_graph(g,n, maxd=1):
    neighs=set([n])
    nodes=neighs
    for d in range(1,maxd+1):
        newnodes=set()
        for node in nodes:
            for neigh in nx.all_neighbors(g,node):
                newnodes.add(neigh)
        nodes=newnodes
        neighs.update(nodes)
    return g.subgraph(neighs)

def save_graph_data(g, header, data, filename):
    f=open(filename,"w")
    f.write(header)
    links=set([d['label'] for u,v,d in g.edges(data=True)])
    for record in data:
        if record[0] in links:
            f.write(",".join(record))
    f.close()

def extract_central_subgraph(filename,maxd=3):
    header,data=load_data(filename)
    g=build_graph(set([record[1] for record in data]))
    center=sorted(g.degree().items(),key=lambda s: s[1],reverse=True)[0][0]
    newg=build_neighbourhood_graph(g,center,maxd)
    #draw_graph(newg,title="%d-neighbourhood of node %s" %(maxd,center),filename="results/%s_%d.png" %(center,maxd))
    save_graph_data(newg, header, data, filename="tmp/" + center+".csv")
    return center

def add_travel_time(g, periods, data):    
    for record in data:
        link=record[1]
        period=record[3]
        duration=int(float(record[4]))
        m=re.match(".* between (.*) and (.*) \((.*)\)",link)
        if not m:
            print "ERROR: unmatched link '" + link + "', exiting.."
            sys.exit(0)
        beg=m.groups()[0].replace(' ','_')
        end=m.groups()[1].replace(' ','_')
        if not g.has_edge(beg,end) or not period in periods:
            continue
        if not g.edge[beg][end].has_key('duration'):
            g.edge[beg][end]['duration']=duration
            g.edge[beg][end]['counts']=1
            g.edge[beg][end]['min_duration']=duration
            g.edge[beg][end]['max_duration']=duration
        else:
            g.edge[beg][end]['duration']+=duration
            g.edge[beg][end]['counts']+=1
            if g.edge[beg][end]['min_duration'] > duration:
                g.edge[beg][end]['min_duration']=duration
            if g.edge[beg][end]['max_duration'] < duration:
                g.edge[beg][end]['max_duration']=duration

    # compute average duration per link
    for beg,end,attr in g.edges(data=True):
        attr['duration'] /= attr['counts']
            

def extract_shortestpath_subgraph(g, nodes):
    newg = nx.DiGraph()
    for beg in nodes:
        for end in nodes:
            if beg != end:
                newg.add_edge(beg,
                              end,
                              duration=nx.shortest_path_length(g,source=beg,target=end,weight='duration'),
                              min_duration=nx.shortest_path_length(g,source=beg,target=end,weight='min_duration'),
                              max_duration=nx.shortest_path_length(g,source=beg,target=end,weight='max_duration'))
    return newg

def print_path_lengths(g, beg, stops, end):
    for perm in itertools.permutations(stops):
        print beg,list(perm),end,path_length(g,[beg]+list(perm)+[end])
        
def path_length(g,path,type='mean'):
    length=0
    if type == 'mean':
        edgetype='duration'
    elif type == 'max':
        edgetype='max_duration'
    elif type == 'min':
        edgetype='min_duration'
    else:
        print "Unknown path type %s, exiting" %type
        sys.exit(0)
    for i in range(len(path)-1):
        length+=g.edge[path[i]][path[i+1]][edgetype]
    return length

def build_theory(graph, beg, stops, end, order_constraints, le_constraints, ge_constraints):
    """builds z3+latte theory from graph, start-stops-end nodes, pairwise node ordering constraints,
       less-or-equal and greater-or-equal time constraints"""

    t=Theory()
    
    # integer variable represents ordering of stops
    stops_vars = Ints(" ".join(stops))

    # integer variable represents timing of stops
    stop_time_vars = Ints(" ".join([stop+"_t" for stop in stops]))
    T = Int('T')

    # dictionary mapping var strings to z3 vars
    stops_varmap = dict(zip(stops,stops_vars))
    stop_time_varmap = dict(zip(stops,stop_time_vars))

    # enforcing stops_vars to form a ranking 
    numstops=len(stops)
    for stop_var in stops_vars:
        t.add(stop_var >= 1)
        t.add(stop_var <= numstops)
    for i in range(numstops):
        for j in range(i+1,numstops):
            t.add(stops_vars[i] != stops_vars[j])

    # enforcing order constraints
    for (first,second) in order_constraints:
        t.add(stops_varmap[first] > stops_varmap[second])

    # enforcing less-or-equal constraints
    for (stop,maxtime) in le_constraints:
        t.add(stop_time_varmap[stop] <= maxtime)

    # enforcing greater-or-equal constraints
    for (stop,mintime) in ge_constraints:
        t.add(stop_time_varmap[stop] >= mintime)
        
    # compute arrival time for each stop    
    # consider min and max duration of journey between two stops -> uniform distribution 
    # (can improve with e.g. piecewise linear or so)

    # first block
    for i in range(numstops): 
        t.add(Or(stops_vars[i] != 1,  And(stop_time_vars[i] >= graph[beg][stops[i]]['min_duration'], stop_time_vars[i] <= graph[beg][stops[i]]['max_duration'] )))

    # intermediate blocks
    for b in range(1,numstops): 
        for i in range(numstops): 
            for j in range(numstops): 
                if i == j:
                    continue
                # var[i] == b and var[j] == b+1 => time_var[] + min_dur <= time_var[j] <= time_var[i] + max_dur
                t.add(Or(stops_vars[i] != b,  stops_vars[j] != b+1,  And(stop_time_vars[j] >= stop_time_vars[i] + graph[stops[i]][stops[j]]['min_duration'], 
                                                                         stop_time_vars[j] <= stop_time_vars[i] + graph[stops[i]][stops[j]]['max_duration'])))
    # last block
    for i in range(numstops): 
        t.add(Or(stops_vars[i] != numstops,  And(T >= stop_time_vars[i] + graph[stops[i]][end]['min_duration'], 
                                                 T <= stop_time_vars[i] + graph[stops[i]][end]['max_duration'])))

    return t

def onehot_encoding(t,bool_vars,sat_varmap=None):
    numvars=len(bool_vars)
    t.add(Or(bool_vars))
    if sat_varmap:
        add_sat_constraint(t,[sat_varmap[str(v)] for v in bool_vars])
    for i in range(numvars):
        for j in range(i+1,numvars):
            t.add(Or(Not(bool_vars[i]), Not(bool_vars[j])))
            if sat_varmap:
                add_sat_constraint(t,[-sat_varmap[str(bool_vars[i])],-sat_varmap[str(bool_vars[j])]])

def add_latte_constraint(t,var_string,lattedim,var_terms,bias_term,less_equal):
    """
    encodes constraint in latte format and adds it to theory. Returns 1 if constraint is correctly created
    latte encoding for Ax <= b is b -A
    """
    vec=[0]*lattedim

    if less_equal:
        vec[0]=bias_term
        for (k,v) in var_terms.items():
            vec[k+1]=-v
    else:
        vec[0]=-bias_term
        for (k,v) in var_terms.items():
            vec[k+1]=v
            
    constraint=" ".join(["%.0f" %val for val in vec])

    t.ld[var_string]=constraint
    t.pwd[var_string]="1"

    return 1

def add_sat_constraint(t,terms):
    """
    dimacs format: CNF, '-' for negated literals, zero terminated lines. E.g.:
    c A sample .cnf file.
    p cnf 3 2
    1 -3 0
    2 3 -1 0 
    """
    t.cnf_formulas.append(" ".join([str(term) for term in terms]) + " 0\n")


def build_boolean_theory(problem,duration_constraint=None):
    """builds z3+latte theory from graph, start-stops-end nodes, pairwise node ordering constraints,
       less-or-equal and greater-or-equal time constraints"""

    t=Theory()
    numstops=len(problem.stops)    
    stops_varmap={}
    bool_vars=[]
    stops_sat_varmap={}

    # boolean variable represents ordering of stops
    for i in range(1,numstops+1):
        curr_stops_varstrings = ["%s_%d" %(s,i) for s in problem.stops]
        curr_stops_vars = Bools(" ".join(curr_stops_varstrings))

        # map varstrings to vars
        for (s,v) in zip(curr_stops_varstrings,curr_stops_vars):
            stops_varmap[s]=v        

        # add decision vars 
        bool_vars.extend(curr_stops_vars)

    # mapping between z3 and crpytominisat vars
    stops_sat_varmap = dict(zip([str(bool_var) for bool_var in bool_vars],range(1,len(bool_vars)+1)))
    t.cnf2smt_varmap = dict(zip(range(1,len(bool_vars)+1),bool_vars))

    # integer variable represents timing of stops
    stop_time_vars = Ints(" ".join([stop+"_t" for stop in problem.stops]))
    T = Int('T')
    stop_time_varmap = dict(zip(problem.stops,stop_time_vars))

    # enforcing one-hot encoding of stops_vars
    for i in range(numstops):
        # one-hot encoding over stops
        stop_vars=bool_vars[(i*numstops):(i*numstops)+numstops]
        onehot_encoding(t,stop_vars,stops_sat_varmap) 
        # one-hot encoding over time instants
        time_vars=[bool_vars[j] for j in range(len(bool_vars)) if (j-i) % numstops == 0]
        onehot_encoding(t,time_vars,stops_sat_varmap) 

    # enforcing order constraints
    for (first,second) in problem.order_constraints:
        for i in range(1,numstops+1):
            for j in range(i+1,numstops+1): 
                stop_var_i_s="%s_%d" %(first,i)
                stop_var_j_s="%s_%d" %(second,j)
                t.add(Or(Not(stops_varmap[stop_var_i_s]), Not(stops_varmap[stop_var_j_s])))
                add_sat_constraint(t,[-stops_sat_varmap[stop_var_i_s],-stops_sat_varmap[stop_var_j_s]])

    # creating latte decision variables
    lattedim=numstops+2 # includes T and bias term
    numconstraints=len(problem.le_constraints)+len(problem.ge_constraints)+4*numstops+2*(numstops-1)*(numstops*numstops-numstops)
    if duration_constraint:
        numconstraints+=1
    latte_var_strings=["l_%d" %i for i in range(numconstraints)]
    latte_vars=Bools(" ".join(latte_var_strings))
    t.dvars=latte_vars
    curr_const=0

    # enforcing less-or-equal constraints
    for (stop,maxtime) in problem.le_constraints:
        t.add(latte_vars[curr_const] == (stop_time_varmap[stop] <= maxtime))
        t.add(latte_vars[curr_const])
        curr_const+=add_latte_constraint(t,latte_var_strings[curr_const],lattedim,{problem.stops.index(stop):1},maxtime,True)

    # enforcing greater-or-equal constraints
    for (stop,mintime) in problem.ge_constraints:
        t.add(latte_vars[curr_const] == (stop_time_varmap[stop] >= mintime))
        t.add(latte_vars[curr_const])
        curr_const+=add_latte_constraint(t,latte_var_strings[curr_const],lattedim,{problem.stops.index(stop):1},mintime,False)
                    
    # compute arrival time for each stop    
    # consider min and max duration of journey between two stops -> uniform distribution 
    # (can improve with e.g. piecewise linear or so)

    # first block
    for i in range(numstops): 
        stop_var_s="%s_%d" %(problem.stops[i],1)        
        t.add(If(stops_varmap[stop_var_s],And(latte_vars[curr_const],latte_vars[curr_const] == (stop_time_vars[i] >= problem.graph[problem.beg][problem.stops[i]]['min_duration'])),latte_vars[curr_const] == False))                 
        curr_const+=add_latte_constraint(t,latte_var_strings[curr_const],lattedim,{i:1},problem.graph[problem.beg][problem.stops[i]]['min_duration'],False)
        t.add(If(stops_varmap[stop_var_s],And(latte_vars[curr_const],latte_vars[curr_const] == (stop_time_vars[i] <= problem.graph[problem.beg][problem.stops[i]]['max_duration'])),latte_vars[curr_const] == False))                 
        curr_const+=add_latte_constraint(t,latte_var_strings[curr_const],lattedim,{i:1},problem.graph[problem.beg][problem.stops[i]]['max_duration'],True)      

    # intermediate blocks
    for b in range(1,numstops): 
        for i in range(numstops): 
            for j in range(numstops): 
                if i == j:
                    continue
                # var[i] == b and var[j] == b+1 => time_var[i] + min_dur <= time_var[j] <= time_var[i] + max_dur
                svar_b="%s_%d" %(problem.stops[i],b)
                svar_e="%s_%d" %(problem.stops[j],b+1)
                t.add(If(And(stops_varmap[svar_b],stops_varmap[svar_e]),
                         And(latte_vars[curr_const],latte_vars[curr_const] == (stop_time_vars[j] >= stop_time_vars[i] + problem.graph[problem.stops[i]][problem.stops[j]]['min_duration'])),
                         latte_vars[curr_const] == False))
                curr_const+=add_latte_constraint(t,latte_var_strings[curr_const],lattedim,{j:1,i:-1},problem.graph[problem.stops[i]][problem.stops[j]]['min_duration'],False)
                t.add(If(And(stops_varmap[svar_b],stops_varmap[svar_e]),
                         And(latte_vars[curr_const],latte_vars[curr_const] == (stop_time_vars[j] <= stop_time_vars[i] + problem.graph[problem.stops[i]][problem.stops[j]]['max_duration'])),
                         latte_vars[curr_const] == False))
                curr_const+=add_latte_constraint(t,latte_var_strings[curr_const],lattedim,{j:1,i:-1},problem.graph[problem.stops[i]][problem.stops[j]]['max_duration'],True)

    # last block
    for i in range(numstops): 
        stop_var_s="%s_%d" %(problem.stops[i],numstops)
        t.add(If(stops_varmap[stop_var_s],And(latte_vars[curr_const],latte_vars[curr_const] == (T >= stop_time_vars[i] + problem.graph[problem.stops[i]][problem.end]['min_duration'])),latte_vars[curr_const] == False))
        curr_const+=add_latte_constraint(t,latte_var_strings[curr_const],lattedim,{numstops:1,i:-1},problem.graph[problem.stops[i]][problem.end]['min_duration'],False)
        t.add(If(stops_varmap[stop_var_s],And(latte_vars[curr_const],latte_vars[curr_const] == (T <= stop_time_vars[i] + problem.graph[problem.stops[i]][problem.end]['max_duration'])),latte_vars[curr_const] == False))
        curr_const+=add_latte_constraint(t,latte_var_strings[curr_const],lattedim,{numstops:1,i:-1},problem.graph[problem.stops[i]][problem.end]['max_duration'],True)

    # enforce duration constraint
    if duration_constraint:
        thres=problem.duration
        less_equal=(duration_constraint == "le")
        if less_equal:
            t.add(latte_vars[curr_const] == (T <= thres))
        else:
            t.add(latte_vars[curr_const] == (T >= thres))
        t.add(latte_vars[curr_const])
        curr_const+=add_latte_constraint(t,latte_var_strings[curr_const],lattedim,{numstops:1},thres,less_equal)

    return t
   
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
        # Mapping between SAT CNF and SMT Boolean decision variables (for z3/cryptominisat interface)
        self.cnf2smt_varmap = []
        # Set of formulas in cnf for the SAT solver (cryptominisat)
        self.cnf_formulas = []

    def add(self, e):
        self.s.add(e)

    def save_cnf_formulas(self, filename):
        f=open(filename,"w")
        f.write('c cnf file for traffic congestion data\n')
        f.write('p cnf %d %d\n' %(len(self.cnf2smt_varmap),len(self.cnf_formulas)))
        f.writelines(self.cnf_formulas)


class Problem:
    """
    example of problem, something like:
     path=['A6','A413','A421','A52','A5199','A14']
    order_constraints=[('A52','A5199')]
    le_constraints=[('A421',1800),('A52',3000)]
    ge_constraints=[('A413',2700),('A52',1800)]
    duration=3600
    """
    def __init__(self, problem=None):
        if problem:
            self.path=problem.path
            self.beg=problem.beg
            self.end=problem.end
            self.stops=problem.stops
            self.duration=problem.duration
            self.graph=problem.graph
            self.order_constraints=deepcopy(problem.order_constraints)
            self.le_constraints=deepcopy(problem.le_constraints)
            self.ge_constraints=deepcopy(problem.ge_constraints)
        else:
            self.path=[]
            self.beg=None
            self.end=None
            self.stops=[]
            self.duration=0
            self.graph=None
            self.order_constraints=[]
            self.le_constraints=[]
            self.ge_constraints=[]

    def __str__(self):
        problemstring="path: " + ",".join(self.path) + "\n"
        problemstring+="max_duration: %d\n" %self.duration 
        problemstring+="order_constraints: " + ",".join(["(%s > %s)" %(aft,bef) for (aft,bef) in self.order_constraints]) + "\n"
        problemstring+="le_constraints: " + ",".join(["(%s <= %d)" %(stop,thres) for (stop,thres) in self.le_constraints]) + "\n"
        problemstring+="ge_constraints: " + ",".join(["(%s >= %d)" %(stop,thres) for (stop,thres) in self.ge_constraints]) + "\n"
        return problemstring

    def get_num_constraints(self):
        return len(self.order_constraints)+len(self.le_constraints)+len(self.ge_constraints)

    def get_num_edges(self):
        return len(self.stops)+1

    def get_path_length(self):
        return len(self.path)-1

class ProblemFactory:

    def __init__(self,graph,center,seed=0):
        self.graph=graph
        self.center=center
        random.seed(seed)

    def generate_problem(self,length,num_order_constraints,num_le_constraints,num_ge_constraints):
        problem=Problem()
        problem.beg=self.center
        nodes=self.graph.nodes()
        
        # generate path
        nodes.remove(problem.beg)
        problem.stops=random.sample(nodes,length-2)
        problem.end=problem.beg
        problem.path=[problem.beg]+problem.stops+[problem.end]

        # generate order constraints
        problem.order_constraints=random.sample(list(itertools.permutations(problem.stops,2)),num_order_constraints)
        
        # compute distances
        problem.graph=extract_shortestpath_subgraph(self.graph,problem.path)

        # generate duration constraint
        problem.duration=path_length(problem.graph,problem.path)

        # generate le constraints
        le_nodes=random.sample(problem.stops,num_le_constraints)
        le_thres=random.sample(range(1,len(problem.path)),num_le_constraints)
        problem.le_constraints=[(n,problem.duration/t) for n,t in zip(le_nodes,le_thres)]

        # generate ge constraints
        ge_nodes=random.sample(problem.stops,num_ge_constraints)
        ge_thres=random.sample(range(1,len(problem.path)),num_ge_constraints)
        problem.ge_constraints=[(n,problem.duration/t) for n,t in zip(ge_nodes,ge_thres)]

        return problem

    def generate_set_of_problems(self,length,max_num_constraints,simplified=True):

        problem=Problem()
        problem.beg=self.center
        nodes=self.graph.nodes()
        
        # generate path
        nodes.remove(problem.beg)
        problem.stops=random.sample(nodes,length-2)
        problem.end=problem.beg
        problem.path=[problem.beg]+problem.stops+[problem.end]

        # compute distances
        problem.graph=extract_shortestpath_subgraph(self.graph,problem.path)

        # generate duration constraint
        problem.duration=path_length(problem.graph,problem.path)
        if simplified:
            dur_offset=problem.duration/problem.get_num_edges()
            range_offset=1
        else:
            dur_offset=0
            range_offset=0
        # readjust based on number of constraints
        problem.duration+=dur_offset*max_num_constraints

        # first problem is unconstrained
        problem_set=[problem]

        # generate order constraints
        order_constraints=random.sample(list(itertools.permutations(problem.stops,2)),max_num_constraints/2)        
        
        # generate le constraints
        le_constraints_num=random.randint(0,max_num_constraints/2)
        le_nodes=random.sample(problem.stops,le_constraints_num)
        le_thres=random.sample(range(1,len(problem.path)-range_offset),le_constraints_num)
        le_constraints=[(n,problem.duration/t-dur_offset) for n,t in zip(le_nodes,le_thres)]

        # generate ge constraints
        ge_constraints_num=max_num_constraints/2-le_constraints_num
        ge_nodes=random.sample(problem.stops,ge_constraints_num)
        ge_thres=random.sample(range(1+range_offset,len(problem.path)),ge_constraints_num)
        ge_constraints=[(n,problem.duration/t+dur_offset) for n,t in zip(ge_nodes,ge_thres)]

        # generate problems with increasing number of constraints
        le_const=True
        for c in range(max_num_constraints/2):
            newproblem = Problem(problem_set[-1])
            newproblem.order_constraints.append(order_constraints[c])            
            if len(le_constraints):
                if le_const or not len(ge_constraints):
                    newproblem.le_constraints.append(le_constraints.pop())
                    le_const = False
                else:
                    newproblem.ge_constraints.append(ge_constraints.pop())
            else:
                newproblem.ge_constraints.append(ge_constraints.pop())
            problem_set.append(newproblem)

        return problem_set


def toy_problem(g):
    # 1 start from A6
    # 2 pass by A413, A421, A52, A5199 (not necessarily in this order)
    # 3 start at 8 am (time period 32)
    # 4 reach A421 within 8:30 
    # 5 reach A413 after 8:45 
    # 6 reach A52 between 8:30 and 8:50 
    # 7 reach A5199 after A52
    # 8 reach A14 before 9:00 
    # P(8|1-7)
    problem=Problem()
    problem.path=['A6','A413','A421','A52','A5199','A6']
    problem.graph=extract_shortestpath_subgraph(g, problem.path)
    problem.beg,problem.stops,problem.end=problem.path[0],problem.path[1:-1],problem.path[-1]
    problem.order_constraints=[('A52','A5199')]
    problem.le_constraints=[('A421',1800),('A52',3000)]
    problem.ge_constraints=[('A413',2700),('A52',1800)]
    problem.duration=3600
    return problem

def toy_problem_set(g):
    problem=Problem()
    problem.path=['A6','A14','A1304','A43','A5199','A6']
    problem.graph=extract_shortestpath_subgraph(g, problem.path)
    problem.beg,problem.stops,problem.end=problem.path[0],problem.path[1:-1],problem.path[-1]
    problem.duration=3600
    problem_set=[problem]

    #draw_graph(g,title="2-neighbourhood of node %s" %problem.beg,filename="results/A6_2.png",selected_nodes=problem.path)

    # generate problems with increasing number of constraints
    newproblem = Problem(problem_set[-1])
    newproblem.order_constraints=[('A14','A1304')]
    problem_set.append(newproblem)
    newproblem = Problem(problem_set[-1])
    newproblem.ge_constraints=[('A1304',1800)]
    problem_set.append(newproblem)
    newproblem = Problem(problem_set[-1])
    newproblem.ge_constraints.append(('A5199',1800))
    problem_set.append(newproblem)

    return problem_set

def solve_problem(problem,problem_name,tilt):

    print "Evaluating theory for P(query AND evidence)"
    t=build_boolean_theory(problem,"le")
    vol_pos=volume(t.s,t.pwd,t.ld,t.bounds,t.dvars)
    t=build_boolean_theory(problem,"le")
    approx_vol_pos=approximate_volume(t,problem_name,tilt)
    print "exact volume=%f approx volume=%f difference(%%)=%f" %(vol_pos,approx_vol_pos,(vol_pos-approx_vol_pos)/vol_pos)

    print "Evaluating theory for P(NOT query AND evidence)"
    t=build_boolean_theory(problem,"ge")
    vol_neg=volume(t.s,t.pwd,t.ld,t.bounds,t.dvars)
    t=build_boolean_theory(problem,"ge")
    approx_vol_neg=approximate_volume(t,problem_name,tilt)
    print "exact volume=%f approx volume=%f difference(%%)=%f" %(vol_neg,approx_vol_neg,(vol_neg-approx_vol_neg)/vol_neg)

    print "EXACT P(query|evidence) = %f" % (vol_pos/(vol_pos+vol_neg))
    print "APPROX P(query|evidence) = %f" % (approx_vol_pos/(approx_vol_pos+approx_vol_neg))

def solve_problem_set(problem_set,problem_name,tilt,exact=False,reverse=False):

    curr_problem_set=problem_set
    
    if reverse:
        # reverse order, from most to least constrained, to early recognize unfeasibility
        curr_problem_set.reverse()

    for problem in curr_problem_set:
        print problem
        start_time = time.time()
        t=build_boolean_theory(problem,"le")
        approx_vol_pos=approximate_volume(t,problem_name,tilt)
        t=build_boolean_theory(problem,"ge")
        approx_vol_neg=approximate_volume(t,problem_name,tilt)   
        end_time = time.time()
        print "APPROX P(query|evidence) = %f" % (approx_vol_pos/(approx_vol_pos+approx_vol_neg))
        print_problem_stats(problem,t)
        print "Elapsed time was " + str(end_time - start_time)      
        if exact:
            start_time = time.time()
            t=build_boolean_theory(problem,"le")
            vol_pos=volume(t.s,t.pwd,t.ld,t.bounds,t.dvars)
            print "exact volume=%f approx volume=%f difference(%%)=%f" %(vol_pos,approx_vol_pos,(vol_pos-approx_vol_pos)/vol_pos)
            t=build_boolean_theory(problem,"ge")
            vol_neg=volume(t.s,t.pwd,t.ld,t.bounds,t.dvars)
            print "exact volume=%f approx volume=%f difference(%%)=%f" %(vol_neg,approx_vol_neg,(vol_neg-approx_vol_neg)/vol_neg)
            end_time = time.time()
            print "EXACT P(query|evidence) = %f" % (vol_pos/(vol_pos+vol_neg))
            print_problem_stats(problem,t)
            print "Elapsed time was " + str(end_time - start_time)      


def print_problem_stats(problem,t):
    print "Problem path length was " + str(problem.get_path_length())
    print "Number of cnf constraints was " + str(problem.get_num_constraints())
    print "Size of theory was " + str(len(t.s.assertions()))
    print "Problem size was " + str(len(t.cnf_formulas))


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
    CountEstimate, wmi, wmax = ApproxWMI(runIndex, timeout, initialFileName, numVariables, numClauses, pivot, numIterations, tilt, shouldLog,logFileName,initialFileNameSuffix, t)
    # print results
    OutputResult(epsilon,delta, CountEstimate, wmi, wmax, outputFileName)
    print "done computing approx WMI"

    return wmi


if __name__ == "__main__":

    if len(sys.argv) < 5:
        print "Usage: " + sys.argv[0] + " <srcfile> <maxd> <toy/random> <tilt> [<rand_length> <rand_maxconst>]"
        sys.exit(0)

    srcfile=sys.argv[1]
    maxd=int(sys.argv[2])
    probtype=sys.argv[3]
    tilt=int(sys.argv[4])
    if probtype != "toy" and probtype != "random":
        print "ERROR: unknown problem type, expected 'toy' or 'random', got '%s'" %probtype
        sys.exit(0)
    if probtype == "random":
        if len(sys.argv) < 7:
            print "Usage with random: " + sys.argv[0] + " <srcfile> <maxd> random <tilt> <rand_length> <maxconst>"
            sys.exit(0)
        length=int(sys.argv[5])
        max_num_constraints=int(sys.argv[6])
        
    # function to extract subgraph around node with highest degree
    problem_name=extract_central_subgraph(srcfile,maxd)
    datafile="tmp/"+problem_name+'.csv'
    header,data=load_data(datafile)
    g=build_graph(set([record[1] for record in data]))
    add_travel_time(g, ['32','33','34','35'], data)
    
    # try out toy problem
    if probtype=='toy':
        solve_problem_set(toy_problem_set(g),'toy',tilt,exact=True,reverse=False)
    
    else:
        # problem factory
        factory=ProblemFactory(g,problem_name)
    
        # try out set of random problems
        feasible=False
        while not feasible:
            print "Looking for feasible problem set"
            problem_set=factory.generate_set_of_problems(length,max_num_constraints)
            feasible=check_feasibility(problem_set[-1])
        print "Feasible problem set found"
        solve_problem_set(problem_set,problem_name,tilt,exact=True,reverse=True)

