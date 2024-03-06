#!/bin/bash

POSITIONAL=()

REMOTE=false
INSTALL=false

while [[ $# -gt 0 ]]; do
  key="$1"

  case $key in
    -r|--remote)
      REMOTE=true
      shift # past argument
      ;;
    -i|--install)
      INSTALL=true
      shift # past argument
      ;;
    *)    # unknown option
      POSITIONAL+=("$1") # save it in an array for later
      shift # past argument
      ;;
  esac
done

if [ "$REMOTE" = true ] ; then
  git submodule update --init --recursive --remote
else
  git submodule update --init --recursive
fi

if test -f ppcg/autogen.sh; then
	(cd ppcg; ./autogen.sh)
fi

./autogen.sh
cd ./ppcg/isl && bash ../../build_submodule.sh && cd ../..
cd ./ppcg && bash autogen.sh && ./configure && make -j$(nproc) && cd ..
mkdir install
./configure --prefix=`pwd`/install --enable-inner
make -j$(nproc)
make install
