export QUARK_CROOT=`pwd`/test/quark
export PYTHONPATH=$QUARK_CROOT/common:$QUARK_CROOT/input
mkdir $QUARK_CROOT/log &> /dev/null
cd ml
./kernel
