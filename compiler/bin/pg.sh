#!/usr/bin/env bash

# start proof general with necessary coq options
# adapted from "pg" script in CompCert

function quote {
  printf "\"%s\" " $@
}

function canonpath {
  echo $(cd $(dirname $1); pwd -P)/$(basename $1)
}

function setup_paths {
  for p in $@; do
    if [ ! -f $p ]; then
      touch $p
    fi
    canonpath $p
  done
}

if [ "$(uname)" = "Darwin" ]; then
  EMACS="open -a /Applications/Emacs.app --args"
else
  EMACS=emacs
fi

YNOT="$KRAKEN/compiler/ynot/src/coq"

COQTOP="coqtop"
COQARGS=$(quote -R $YNOT Ynot)

$EMACS \
  -eval "(setq coq-prog-name \"$COQTOP\")" \
  -eval "(setq coq-prog-args '($COQARGS))" \
  $(setup_paths $@)
