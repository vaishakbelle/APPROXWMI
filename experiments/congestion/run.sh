
lengths="6 7 8"
tilt=5
for l in $lengths
do
  echo "Problem length: $l"
  problem=A6_${l}_6
  python run.py "data/Sep 2014.csv" 3 random $tilt $l 6 > results/$problem.log
  cat results/$problem.log | grep -e EXACT -e APPROX -A 5 > results/$problem.stats
  python results/volume_computations.py results/$problem.log > results/$problem.vol
done
