cd /home/ucsd/kraken/reflex/coq/bench-quark
ROOT=`pwd`
export QUARK_CROOT=$ROOT/test/quark
export PYTHONPATH=$QUARK_CROOT/common:$QUARK_CROOT/input
cd $QUARK_CROOT/common
./create_config.py
mkdir $QUARK_CROOT/log &> /dev/null
cd $ROOT/ml
./kernel
