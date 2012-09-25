#!/usr/bin/env bash

# start proof general with necessary coq options
# adapted from "pg" script in CompCert

function error {
  echo ERROR : $*
  exit 1
}

if [ ! -f $KRAKEN/.kraken-root ]; then
  error "\$KRAKEN must point to root of Kraken repository."
fi

YNOT=$COMPILER/ynot/src/coq

if [ "$(uname)" = "Darwin" ]; then
  EMACS="open -a /Applications/Emacs.app --args"
else
  EMACS=emacs
fi

function canonpath {
  echo $(cd $(dirname $1); pwd -P)/$(basename $1)
}

function quote {
  printf "\"%s\" " $@
}

function setup_paths {
  for p in $@; do
    if [ ! -f $p ]; then
      touch $p
    fi
    canonpath $p
  done
}

COQTOP="coqtop"
COQARGS=$(quote -R $YNOT Ynot)

$EMACS \
  -eval "(setq coq-prog-name \"$COQTOP\")" \
  -eval "(setq coq-prog-args '($COQARGS))" \
  $(setup_paths $@)
