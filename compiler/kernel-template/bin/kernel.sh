#!/usr/bin/env bash

export KROOT="__KROOT__"
export PYTHONPATH="$PYTHONPATH:$KROOT/lib/python2.7/site-packages"

EXEC="$KROOT/bin/.Main"
if [ "$1" = "--debug" ]; then
  EXEC="ocamldebug -I $KROOT/ml/_build $EXEC"
fi
$EXEC
