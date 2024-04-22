# PPCG and PET path for CorePPT to launch
ppcg_bin=`pwd`/ppcg/install/bin
# path of the simulation binary
obj_dir=/home/dreyex/use_this/obj
# could choose MINI_DATASET, SMALL_DATASET, MEDIUM_DATASET, LARGE_DATASET, EXTRALARGE_DATASET
data_size=MEDIUM_DATASET

# Simulate all the binary in the obj directory
for i in `ls $obj_dir`
do
    ./CorePPT $obj_dir/$i $ppcg_bin -D$data_size
done