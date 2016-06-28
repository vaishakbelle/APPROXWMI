# Code is adapted by Vaishak Belle to do WMI 
# Notes: adapted from http://arxiv.org/pdf/1404.2984, Distribution-Aware Sampling and Weighted Model Counting for SAT. Supratik Chakraborty, Daniel J. Fremont, Kuldeep S. Meel, Sanjit A. Seshia, and Moshe Y. Vardi. Proceedings of AAAI Conference on Artificial Intelligence (AAAI), 2014.  


import sys
import os
import math
import re
import random
import time
from z3 import *
#from pdb import set_trace as stop 

# import volume computation code 
# sys.path.insert(0, '../')
from vol import *

#Requirements : doalarm should print something that indicates timeout. For now lets say that command
#Variables are indexed from 1 to N not 0 to N-1
#Initialization : Ensure there exists a log/results & log/inputFiles folder in the parent directory
fileaddOfRandom = ''
fileaddOfRandPickTable = ''
randPickTable = {} #For every key k, the numbers m and n such that 2^n mod m gives the most efficient way of picking a random number from 0 to k-1 
randTotalLen = 0
randData = ''
randIndex = 0
TMPDIR = "tmp"
def ensureDirectory(path):
    d = os.path.dirname(path)
    if not os.path.exists(d):
        os.makedirs(d)
def usage():
    usageStr = "Usage: python ApproxMC.py [options] <inputfile>\n"
    usageStr += "options are entered as -object=value where object can be \n"
    usageStr += "timeout: timeout for iteration in seconds (default:3000 seconds)\n"
    usageStr += "delta: the value of parameter delta\n"
    usageStr += "epsilon: the value of the parameter epsilon\n"
    usageStr += "tilt: the value of tilt parameter\n"
    usageStr += "numSamples: Number of samples (value of t in the algorithm), note that this overrides the value of t calculated from the delta\n"
    usageStr += "logging: 0/1 : 0 for turnoff and 0 for turn on. In case logging is turned on, the log file wil be present in log/logging\n"
    usageStr += "outputFile: (optional) supply the output file destination\n"
    usageStr += "log: (optional) supply the log file destination (deafult : log/logging/<inputFileName>.txt)\n"
    usageStr += "runIndex: this will be used as indicator If you are running multiple copies of ths script in"
    usageStr += "parallel, you MUST supply a different runIndex option for each of them\n"
    print usageStr
    exit(1)
def bin(x):
    if x<0:
        return '-'+bin(-x)
    out = []
    if (x == 0):
        out.append('0')
    while (x>0):
        out.append('01'[x&1])
        x >>= 1
        pass
    try:
        return ''.join(reversed(out))
    except NameError,ne2:
        out.reverse()   
    return ''.join(out)
def getBinary(binLen):
    byteLen = 1+binLen/8
    _random_source = open("/dev/urandom","rb")
    randBytes = _random_source.read(byteLen)
    _random_source.close()

    randInt = int(randBytes.encode("hex"),16)
    randBin = bin(randInt).zfill(binLen)
    return randBin[:binLen]

def getRandomNum(totalCount):
    global randPickTable,randData,randIndex,randTotalLen
    modNum = int(randPickTable[totalCount][0])
    powerNumBits = int(randPickTable[totalCount][1])
    while(True):
        randBits  = getBinary(powerNumBits)
        powerNum = int(randBits,2) 
        if (powerNum < modNum*totalCount):
            return powerNum%totalCount
def init():
    global TMPDIR
    ensureDirectory("log/results/")
    ensureDirectory(TMPDIR+"/")
    ensureDirectory(TMPDIR+"/inputFiles/")
    ensureDirectory("log/logging/")


''' compute BoundedWeightSat given formula (i.e. o/p of cryptominisat), r, wmax'''

def bwsat(lines, pivot, r, wmax,t): 
    # nos models and wmi
    valCount = 0 
    wmi = 0 
    
    # min. model weight 
    wmin = float(wmax/r)
        
    for line in lines: 
        # check if crypto model is LRA-consistent, and get volume 
        cons, vol = assert_and_getvol(t, line.strip('\n').strip('v '))
        #stop()
        valCount += cons
        # line 8 of algo 3
        wmi += vol
        # if model is theory consistent, update wmin 
        # line 9 of algo 3
        if ((cons == 1) and (vol !=0)): 
            wmin = min(wmin, vol)

        # repeat until vol/w_max > pivot
        if (wmi / (wmin*r)) > pivot:
            break

    # line 11 of algo 3    
    return valCount, wmi, wmin*r

    
# Returns 0 when its solvable, 1 when number of solutions are larger than maxSolutions, 2 when timeout occurs,3 
# @v: returns model count and wmi as well 
# @v: input send solver instance 
def WMICore(fileName, numVariables, maxSolutions, tilt, wmax, timeout,runIndex,hashCount,fileNameSuffix, t):
    global TMPDIR
    outputFileName = TMPDIR+"/res_"+str(fileNameSuffix)+"_"+str(runIndex)+"_"+str(numVariables)+'_'+str(hashCount)+".txt"
    noSolutions = True
    cmd = ''
    wmi = 0
    noSolStr = 's UNSATISFIABLE'

    if (noSolutions):
        noSolStr = 'c UNSATISFIABLE'
        cmd = "./doalarm -t profile "+str(timeout)+" ./cryptominisat --gaussuntil=400 --maxsolutions="+str(maxSolutions+1)+" --verbosity=0 "+str(fileName)+"| grep \"v \""+" > "+str(outputFileName) 
    else:
        cmd = "./doalarm -t profile "+str(timeout)+" ./cryptominisat --gaussuntil=400 --maxsolutions="+str(maxSolutions+1)+" --verbosity=0 "+str(fileName)+" > "+str(outputFileName)
    starttime = time.time()
    #print cmd
    os.system(cmd)
    endtime = time.time()
    #sometimes the times are off, so just additional sanity check
    if (endtime-starttime >timeout-10):
        return 2,0
    res = []
    f = open(outputFileName,'r')
    lines = f.readlines()
    f.close()
    os.system('rm '+outputFileName)

    if (lines!=[]):
        res = lines[len(lines)-1]
        #When timeout occurs
        if (res.strip() == 'Alarm clock: 14'):
            return 2,0
        if (lines[0].strip() == noSolStr):
            return 3,0

    valCount, wmi, wmax = bwsat(lines, maxSolutions, tilt, wmax,t)

    if (not(noSolutions) and valCount!=0):
        if (lines[len(lines)-1].strip() ==  noSolStr):
            valCount= valCount-1
        valCount = valCount/2
    
    if (wmi / wmax) > maxSolutions: # volume larger than threshold
        return 1, 0, wmi, wmax
    elif not valCount: # no solution
        return 3, valCount, wmi, wmax 
    else:
        return 0, valCount, wmi, wmax 


def findHashBits(numVariables,numHash):
    randBitsTotal = getBinary(numVariables+2*numHash)
    randBits=''
    for i in range(numVariables+1):
        xorResult = 0
        for j in range(numHash):
            xorResult = xorResult^int(randBitsTotal[i+j])
        randBits += str(xorResult)
    return randBits

def findMedian(inputList):
    numList = sorted(inputList)
    medIndex = int((len(numList)+1)/2)
    if (medIndex >= len(numList)):
        return numList[medIndex-1]
    return numList[medIndex]

def findMean(numList):
    sum = 0
    for ele in numList:
        sum += int(ele)
    return (sum*1.0/len(numList))

def findMin(numList):
    min = 100000000
    for ele in numList:
        if (int(ele) < min):
            min = int(ele)
    return min
# This will add hash to the initial File with numHash of XOR clauses! 
def addHash(initialFileName,finalFileName,numVariables,numClauses,numHash):
    hashClauses = ''
    for i in range(int(numHash)):
        varNum = 0
        randBits = findHashBits(numVariables,numHash)
        hashClauses = hashClauses+'x'
        needToNegate = False
        if (randBits[0] == '1'):
            needToNegate = True
        for j in range(1, numVariables+1):
            if (randBits[j] == '1'):
                varNum = varNum+1
                if (needToNegate):
                    hashClauses = hashClauses+'-'
                    needToNegate = False
                hashClauses = hashClauses+str(j)+' '
        hashClauses = hashClauses+' 0\n'
    f = open(initialFileName,'r')
    lines = f.readlines()
    f.close()
    f = open(finalFileName,'w')
    f.write('p cnf '+str(numVariables)+' '+str(numClauses+numHash)+'\n')
    for line in lines:
        f.write(str(line.strip())+'\n')
    if (numHash > 0):
        f.write(hashClauses)
    f.close()
    
    
# Implementation of ApproxWMI with leapfrogging (the leapfrogging call can be improved)
def ApproxWMI(runIndex,timeout,initialFileName,numVariables,numClauses,pivot,numIterations, tilt, shouldLog,logFileName,finalFileName,initialFileNameSuffix, t):

    global fileaddOfRandom,fileaddOfRandPickTable
    f = open(initialFileName,'r')
    lines = f.readlines()
    f.close()
    initialFileNameSuffix =  initialFileName.split('/')[-1][:-4]
    isSolvable = 2
    hashCount = 0
    totalSolutions = 0
    maxSolutions = pivot
    startIteration = 0
    totalSolList = []
    hashCountList = []
    # wmi specific variables 
    wmiSolList = []
    wmaxSolList = []
    # initialize wmax to large number if weights are not normalized
    wmax = 2.0e+15   
    wmi = 0
    for i in range(numIterations):
        isSolvable = 2
        hashCount = startIteration
        countIt = 0
        rat = maxSolutions + 1
        while((rat >  maxSolutions) and (hashCount < numVariables)):
            startTime = time.time()
            # line 9 of algo 2: HXOR(n,i)
            addHash(initialFileName,finalFileName,numVariables,numClauses,hashCount)
            isSolvable, totalSolutions, wmi, wmax = WMICore(finalFileName,numVariables,maxSolutions,tilt, wmax, timeout,runIndex,hashCount,initialFileNameSuffix, t) 
            endTime = time.time()
            timeDiff = endTime-startTime
            logStr = 'ApproxWMI:'+str(i)+':'+str(hashCount)+':'+str(timeDiff)+':'+str(isSolvable)+'\n'
            if (shouldLog):
                g = open(logFileName,'a')
                g.write(logStr)
                g.close()
 
            rat = int(wmi/wmax)
               
            if (isSolvable == 0):
                totalSolList.append(totalSolutions)
                wmiSolList.append(wmi)
                hashCountList.append(hashCount)
                # @vjune removed total count term
                wmaxSolList.append(wmax)
                break
            
            if ((isSolvable == 3) or (isSolvable == 2)):
                countIt +=1
                if (countIt ==4):
                    hashCount = hashCount-5
                    countIt = 0
                else:
                    hashCount = hashCount-1
            hashCount = hashCount+1
        
        
        if (startIteration == 0):
            startIteration = hashCount -5;
            if (startIteration < 0):
                startIteration = 0

                
                
    minHashCount = findMin(hashCountList)
    resultMapList = []
    wmiMapList = []
    wmaxMapList = []
    
    # compute median 
    for i in range(len(hashCountList)):
        resultMapList.append(pow(2,hashCountList[i]-minHashCount)*totalSolList[i])
        wmiMapList.append(pow(2,hashCountList[i]-minHashCount)*wmiSolList[i])
        wmaxMapList.append(pow(2,hashCountList[i]-minHashCount)*wmaxSolList[i])
    medianValue = findMedian(resultMapList)
    wmiMedianValue = findMedian(wmiMapList)
    wmaxMedianValue = findMedian(wmaxMapList)

    return medianValue*pow(2,minHashCount), wmiMedianValue*pow(2,minHashCount), wmaxMedianValue*pow(2,minHashCount)

#returns action(int),error(string),paramMap(dict) where 
#action=0 -> help asked (-h) was supplied show usage menu
#action=1 -> Couldn't understand the argument and error will pass the string
#action=2 -> No inputfile!
#action=3 -> Ready to Go!
#paramMap is for all parameters
def getInputs():
    paramMap={}
    action=0
    error = ''
    acceptedParams={'timeout','logging','runIndex','startIteration','output','log','epsilon','delta'}
    for i in range(1,len(sys.argv)):
        if (not(sys.argv[i][0] == '-')):
            paramMap['inputFile'] = sys.argv[i]
            if (paramMap.has_key('epsilon') and paramMap.has_key('delta')):
                action = 3
                return action,error,paramMap
            else:
                action = 2
                error = "Either 'epsilon' or 'delta' parameter not supplied"
                return action,error,paramMap
        else:
            if (sys.argv[i][1] == 'h'):
                action = 0
                return action,error,paramMap
            fieldValues = sys.argv[i][1:].strip().split('=')
            if (not(fieldValues[0] in acceptedParams)):
                action = 1
                error = "Could not understand the option "+str(fieldValues[0])+"\n"
                return action,error,paramMap
            else:
                paramMap[fieldValues[0]] = fieldValues[1]
    action =2
    error = "No inputfile\n"
    return action,error,paramMap
    
def FindFromTable(delta):
    if (not(os.path.isfile('ProbMapFile.txt'))):
        return 0
    f = open('ProbMapFile.txt','r')
    lines = f.readlines()
    f.close()
    for line in lines:
        fields = line.strip().split(':')
        if (float(fields[1]) > delta):
            return int(fields[0])
    return 0

def OutputResult(epsilon,delta,CountEstimate, wmi, wmax, outputFileName):
    outputStr =  "Approximate count, WMI and WMAX with tolerance: "+str(epsilon)+" and confidence: "+str(1-delta)+" are "+str(CountEstimate)+", "+str(wmi)+" and "+str(wmax)+" respectively"
    if (outputFileName ==''):
        print outputStr
    else:
        f = open(outputFileName,'w')
        f.write(outputStr)
        f.close()

def main():
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
    epsilon = 0
    delta = 0
    tilt = 5.0
    action,error,paramMap = getInputs()
    if (action == 0):
        usage()
        exit(1)
    if (action == 1 or action ==2):
        print error
        exit(1)
    print paramMap
    if (paramMap.has_key('runIndex')):
        runIndex = int(paramMap['runIndex'])
    if (paramMap.has_key('timeout')):
        timeout = float(paramMap['timeout'])+10 #extra protection for time sync
    if (paramMap.has_key('startIteration')):
        startIteration = int(paramMap['startIteration'])
    if (paramMap.has_key('epsilon')):
        epsilon = float(paramMap['epsilon'])
    if (paramMap.has_key('delta')):
        delta = float(paramMap['delta'])
    if (paramMap.has_key('numSamples')):
        numIterations = int(paramMap['numSamples'])
    if (paramMap.has_key('tilt')):
        tilt = int(paramMap['tilt'])
    if (paramMap.has_key('output')):
        outputFileName = paramMap['output']
    if (paramMap.has_key('log')):
        logFileName = paramMap['log']
    if (paramMap.has_key('logging')):
        if (paramMap['logging'] == '0'):
            shouldLog = False
        if (paramMap['logging'] == '1'):
            shouldLog = True
    initialFileName = paramMap['inputFile']
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
    if (logFileName == ''):
        logFileName = "log/logging/log_"+str(initialFileNameSuffix)+'.txt'
    if (shouldLog):
        g = open(logFileName,'w')
        writeStr = 'ApproxWMI:iteration:hashCount:time:isSolvable\n'
        g.write(writeStr)
        g.close()
    finalFileName = TMPDIR+"/inputFiles/input_"+str(initialFileNameSuffix)+'_'+str(runIndex)+".cnf"
    init()
    pivot = 2*math.ceil(4.4817*(1+1/epsilon)*(1+1/epsilon)) 
    numIterations = FindFromTable(1-delta)
    if (numIterations == 0):
        numIterations = int(math.ceil(35*math.log((3*1.0/delta),2)))
        

    t = csv_theory()
    start_time = time.time()
    print 'Exact WMI is ' + str(volume(t.s,t.pwd,t.ld,t.bounds,t.dvars))
    end_time = time.time()
    print("Elapsed time was %g seconds" % (end_time - start_time))

    
    # reinitalize (otherwise constraints carried over)
    tcopy = csv_theory()
    start_time = time.time()
    # computed medians of model count, wmi, and wmax
    CountEstimate, wmi, wmax = ApproxWMI(runIndex, timeout, initialFileName, numVariables, numClauses, pivot, numIterations, tilt, shouldLog,logFileName,finalFileName,initialFileNameSuffix, tcopy)
    os.system('rm '+finalFileName)
    # print results
    OutputResult(epsilon,delta, CountEstimate, wmi, wmax, outputFileName)
    end_time = time.time()
    print("Elapsed time was %g seconds" % (end_time - start_time))


#main()    
