INSTANCES=$(ls instances)

g++ solver.cc -O3 -std=c++11 -o solver

for instance in $INSTANCES
do
	echo "$instance:"
	solver < instances/$instance
done