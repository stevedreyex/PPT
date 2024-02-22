./autogen.sh
mkdir install
./configure --prefix=`pwd`/install
make -j$(nproc)
make install
