import sys

filename=sys.argv[1]
f=open(filename)
num=0
for row in f:
  if row.startswith("current volume"):
    num+=1
  if row.startswith("APPROX"):
    print "Number of volume computations %d" %num
    num=0  
