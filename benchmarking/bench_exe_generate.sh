# This is a file to generate the original size of the program trace
# And the reduced size of the program trace is not yet implemented

# src is the main directory of the benchmark
src=/home/dreyex/Documents/Research/TraceBench
# dst is the directory where the traces will be saved
dst=/home/dreyex/use_that
# could choose MINI_DATASET, SMALL_DATASET, MEDIUM_DATASET, LARGE_DATASET, EXTRALARGE_DATASET
data_size=SMALL_DATASET

list=./benchmark_list_an5d
now=""

for i in `cat $list`
do
    echo "Processing $i"
    now=$(basename $i .c)
    # Line debug
    # echo "Compiling $now from $src/$i $src/utilities/polybench.c to $dst/obj/$now"
    gcc -Og -g -o $dst/obj/$now $src/$i $src/utilities/polybench.c -I $src/utilities -D$data_size -DDATA_TYPE_IS_FLOAT -DPOLYBENCH_USE_SCALAR_LB -DCACHEGRIND
    echo "Compile Succeeded"
    # Version of valgrind don't forget to define the DEBUG macro
done

for i in `cat $list`
do
    now=$(basename $i .c)
    echo "Running $now"
    start_time=$(date +%s)
    ../valgrind/vg-in-place --tool=cachegrind --instr-at-start=no --cache-sim=yes --D1=49152,12,64 --I1=32768,8,64 --L2=1310720,10,64 -v --cachegrind-out-file="cachegrind.out.$now" --log-fd=1  $dst/obj/$now | grep -v "-" | grep -v "=" >  $dst/trace/$now.log
    finish_time=$(date +%s)
    echo "Time duration: $((finish_time - start_time)) secs."
    mv cachegrind.out.$now $dst/trace
done

du -sH $dst/trace/* | sort -n