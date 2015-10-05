
echo "Toy problem"
python run.py "data/Sep 2014.csv" 2 toy > results/toy.log

lengths="6 7 8"
for l in $lengths
do
  echo "Problem length: $l"
  python run.py "data/Sep 2014.csv" 3 random $l 6 > results/A6_${l}_6.log
done

