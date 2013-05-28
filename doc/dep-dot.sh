#!/usr/bin/env bash

DEP=../reflex/coq/.depend

if [ ! -f $DEP ]; then
  echo "Please build Reflex before running this script."
  exit 1
fi

sed -e 's/\([^ ]*\).vo/\1/g' \
    -e 's/[^ ]*\.v//' \
    -e 's/[^ ]*\.glob//' \
    -e 's:[^ /]*/::g' \
    -e 's/:/->/' \
    < $DEP > reflex-dep.dot
