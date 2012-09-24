#!/usr/bin/env bash

# start proof general with necessary coq options
# adapted from "pg" script in CompCert

if [ $# -ne 1 ]; then
  echo Usage : $0 FILE.v
  exit 1
fi

function quote {
  printf "\"%s\" " $*
}

function canonpath () { 
  echo $(cd $(dirname $1); pwd -P)/$(basename $1)
}

if [ "$(uname)" = "Darwin" ]; then
  EMACS="open -a /Applications/Emacs.app --args"
else
  EMACS=emacs
fi

YNOT="$KRAKEN/compiler/ynot/src/coq"

COQTOP="coqtop"
COQARGS=$(quote -I $YNOT -R $YNOT Ynot)

$EMACS \
  -eval "(setq coq-prog-name \"$COQTOP\")" \
  -eval "(setq coq-prog-args '($COQARGS))" \
  $(canonpath $1)
