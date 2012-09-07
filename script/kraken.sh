#!/usr/bin/env bash

function usage {
  echo "
Usage: kraken.sh [options] input.krn

Generate Coq kernel and client libraries from a Kraken spec.

OPTIONS:
  -h, --help        print this usage information
  -f, --force       overwrite existing output
"
  exit 1
}

function error {
  echo "ERROR : $1"
  exit 1
}

if [ ! -f $KRAKEN/.kraken-root ]; then
  error "\$KRAKEN must point to root of Kraken repository."
fi

# http://snipplr.com/view/18026/canonical-absolute-path/
function canonpath () { 
  echo $(cd -P $(dirname "$1"); pwd -P)/$(basename "$1")
}

# arg defaults
FORCE=false
INPUT=""

# process args
if [ "$*" = "" ]; then
  usage
fi
while [ "$*" != "" ]; do
  case $1 in
    "-h" | "-help" | "--help")
      usage
      ;;
    "-f" | "--force")
      FORCE=true
      ;;
    *.krn)
      INPUT=$1
      ;;
    *)
      echo "Unrecognized option '$1'"
      usage
      ;;
  esac
  shift
done

if [ ! -f "$INPUT" ]; then
  error "cannot find input '$INPUT'"
fi
INPUT=$(canonpath "$INPUT")

# setup output dir
cd $KRAKEN/scratch
D=$(basename $INPUT .krn)
if $FORCE; then
  rm -rf $D
elif [ -d $D ]; then
  error "'$D' already exists. To overwrite use --force."
fi
cp -r $KRAKEN/kernel-template $D

# generate code and proofs
$KRAKEN/bin/kraken $INPUT \
  --turn $D/coq/Turn.v \
  --lib $D/lib \
|| error "Kraken compiler failed."

# build the monster
make -C $D
