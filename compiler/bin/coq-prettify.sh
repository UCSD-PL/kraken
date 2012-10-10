#!/usr/bin/env bash

function error {
  echo ERROR : $*
  exit 1
}

if [ ! -f $KRAKEN/.kraken-root ]; then
  error "\$KRAKEN must point to root of Kraken repository."
fi

KBIN=$KRAKEN/compiler/bin

if [ $# -ne 1 ]; then
  echo "Usage : $0 input.v"
  echo "Prettifies Coq source code."
  exit 1
fi

if [ "$(uname)" = "Darwin" ]; then
  EMACS="open -a /Applications/Emacs.app -g --args"
else
  EMACS="emacs -nw -batch"
fi

function canonpath {
  echo $(cd $(dirname $1); pwd -P)/$(basename $1)
}

$EMACS -l ~/.emacs $(canonpath $1) -l "$KBIN/coq-prettify.el" -f 'coq-prettify'
