#!/usr/bin/env bash

if [ "$KRAKEN_GDB" != "" ]; then
  echo "
  break main
  run $@
  " > $KROOT/client/gdb-run
  cgdb $KROOT/client/test -x $KROOT/client/gdb-run
elif [ "$KRAKEN_VALGRIND" != "" ]; then
  valgrind $KROOT/client/test "$@"
else
  $KROOT/client/test "$@"
fi
