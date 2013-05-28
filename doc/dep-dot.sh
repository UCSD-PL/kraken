#!/usr/bin/env bash

DEP=../reflex/coq/.depend

if [ ! -f $DEP ]; then
  echo "Please build Reflex before running this script."
  exit 1
fi

function graph {
  echo "digraph { "
  sed -e 's/\([^ ]*\).vo/\1/g' \
      -e 's/[^ ]*\.v//' \
      -e 's/[^ ]*\.glob//' \
      -e 's:[^ /]*/::g' \
      -e 's/:/->/' \
      $DEP
  echo "labelloc=\"t\""
  echo "label=\"Reflex Module Dependencies ($(date))\""
  echo "}"
}

graph | dot -Tpng > reflex-module-deps.png
