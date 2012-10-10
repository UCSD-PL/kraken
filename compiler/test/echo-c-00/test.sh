#!/usr/bin/env bash

if [ "$KRAKEN_DEBUG" != "" ]; then
  echo "
  break main
  run $@
  " > $KROOT/client/gdb-run

  cgdb $KROOT/client/test -x $KROOT/client/gdb-run
else
  $KROOT/client/test $@
fi
