#!/usr/bin/env bash

export KROOT="__KROOT__"
export PYTHONPATH="$PYTHONPATH:$KROOT/lib/python2.7/site-packages"

if [ "$1" = "--debug" ]; then
  ocamldebug -I $KROOT/ml $KROOT/bin/.Main
else
  $KROOT/bin/.Main
fi
