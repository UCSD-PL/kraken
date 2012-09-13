#!/usr/bin/env bash

function error {
  echo "ERROR : $1"
  exit 1
}

# ensure KRAKEN environment variable is valid
if [ "$KRAKEN" = "" ] || [ ! -f $KRAKEN/.kraken-root ]; then
  error "\$KRAKEN must point to root of Kraken repository."
fi

# default arguments
BUILD=false
FORCE=false
OUTDIR="/tmp"
INPUT=""

function usage {
  echo "
Usage: kraken.sh [options] input.krn

Generate Coq kernel and client libraries from a Kraken spec.

OPTIONS:
  -h, --help          print this usage information
  -b, --build         build generated kernel
  -f, --force         overwrite existing output
  -o, --outdir DIR    generate output in DIR (default: $OUTDIR)
"
  exit 1
}

# http://snipplr.com/view/18026/canonical-absolute-path/
function canonpath () { 
  echo $(cd -P $(dirname "$1"); pwd -P)/$(basename "$1")
}

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
    "-b" | "--build")
      BUILD=true
      ;;
    "-o" | "--outdir")
      shift
      OUTDIR=$1
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

if [ ! -d "$OUTDIR" ]; then
  error "cannot generate output in '$OUTDIR'"
fi

# setup kernel tree dir
D="$OUTDIR/$(basename $INPUT .krn)"
if $FORCE; then
  rm -rf $D
elif [ -d $D ]; then
  error "'$D' already exists. To overwrite use --force."
fi
cp -r $KRAKEN/kernel-template $D

# generate code and proofs
$KRAKEN/bin/kraken $INPUT \
  --turn $D/coq/Turn.v \
  --lib $D/client \
|| error "Kraken compiler failed."

# tell Makefile where it lives
echo "
# path to root of generated kernel
KROOT := $D
" >> $D/Makefile.config

if $BUILD; then
  echo
  echo ">>> BUILDING $D <<<"
  echo
  make -C $D
fi
