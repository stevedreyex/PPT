#!/bin/bash

# Don't forget to modify the dataset size you want to examine
# could choose MINI_DATASET, SMALL_DATASET, MEDIUM_DATASET, LARGE_DATASET, EXTRALARGE_DATASET
data_size=SMALL_DATASET
# src is the main directory of the benchmark
src=/home/dreyex/Documents/Research/TraceBench
# dst is the directory where the traces will be saved
dst=/home/dreyex/trace/use_this
benchmark=./benchmark_list
ppcg_bin=`pwd`/../ppcg/install/bin
now=""

# Function to get the current time in milliseconds
get_current_time() {
    date +%s%N
}

# Function to calculate the elapsed time in seconds with milliseconds precision
calculate_elapsed_time() {
    local start_time=$1
    local end_time=$2
    local elapsed_seconds=$(( (end_time - start_time) / 1000000000 ))
    local elapsed_milliseconds=$(( (end_time - start_time) % 1000000000 / 1000000 ))
    echo "$elapsed_seconds.$elapsed_milliseconds"
}

# Time to generate the trace for simulation
run_test_a() {
    local item_basename=$1
    ../valgrind/vg-in-place --tool=cachegrind --instr-at-start=no --cache-sim=yes --D1=32768,8,64 --L2=2097152,16,64 -v --cachegrind-out-file="cachegrind.out.$item_basename" --log-fd=1  $dst/obj/$item_basename | grep -v "-" | grep -v "=" >  $dst/trace/$item_basename.log
    mv cachegrind.out.$now $dst/trace
}

# Simulation the trace in the CoreSim LRU
run_test_b() {
    local item_basename=$1
    ../src/CoreSim $dst/trace/$item_basename.log
}

# Use polyhedral trace to simulate the trace instead of test_a and test_b
run_test_c() {
    local item_basename=$1
    ../src/CorePPT $dst/obj/$item_basename $ppcg_bin -D$data_size
}

# Initialize arrays to store test timings

echo "Item Generate_trace Simulate_trace Polyhdral_Simulate" > timings.dat

# Iterate through each item in the benchmark list
while IFS= read -r i; do
    echo "" # Line change for better readability
    echo "Processing $i"
    now=$(basename $i .c)
    name_of_test+=$now
    gcc -Og -g -o $dst/obj/$now $src/$i $src/utilities/polybench.c -I $src/utilities -D$data_size -DDATA_TYPE_IS_FLOAT -DPOLYBENCH_USE_SCALAR_LB -DCACHEGRIND
    echo "Compile Succeeded"

    # Execute each test function and collect timings
    start_time=$(get_current_time)
    test_result=("$(run_test_a $now)")
    finish_time=$(get_current_time)
    elapsed_time=$(calculate_elapsed_time "$start_time" "$finish_time")
    echo "Finish generating trace for $now with $elapsed_time seconds."
    test_a_timings=$elapsed_time

    start_time=$(get_current_time)
    test_result=("$(run_test_b $now)")
    finish_time=$(get_current_time)
    elapsed_time=$(calculate_elapsed_time "$start_time" "$finish_time")
    echo "Finish generating trace for $now with $elapsed_time seconds."
    test_b_timings=$elapsed_time


    start_time=$(get_current_time)
    test_result=$(run_test_c $now)
    finish_time=$(get_current_time)
    elapsed_time=$(calculate_elapsed_time "$start_time" "$finish_time")
    echo "Finish generating trace for $now with $elapsed_time seconds."
    echo "$test_result"
    test_c_timings=$elapsed_time

    printf "%s %s %s %s\n" "$now" "$test_a_timings" "$test_b_timings" "$test_c_timings" >> timings.dat

done < $benchmark

du -sH $dst/trace/* | sort -n
rm -rf *.cu *.hu

# Generate bar plot using gnuplot
gnuplot <<- EOF
    set terminal pngcairo enhanced font "arial,10" size 800,600
    set output 'benchmark_plot.png'
    set title "Benchmark Test Timings"
    set ylabel "Time (seconds)"
    set xlabel "Items"
    set xtics rotate by -45
    set style data histogram
    set style histogram cluster gap 1
    set style fill solid 1.0 border -1
    plot 'timings.dat' using 2:xtic(1) title "Test A", '' using 3 title "Test B", '' using 4 title "Test C"
EOF

mv benchmark_plot.png timings.dat ../log_file

echo "Plot generated: benchmark_plot.png in ../log_file"
