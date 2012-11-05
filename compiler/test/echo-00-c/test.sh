#!/usr/bin/env bash

if [ "$GDB" = "" ]; then
  GDB=gdb
fi

if [ "$KRAKEN_GDB" != "" ]; then
  echo "
  break main
  run $@
  " > $KROOT/client/gdb-run
  $GDB $KROOT/client/test -x $KROOT/client/gdb-run
elif [ "$KRAKEN_VALGRIND" != "" ]; then
  valgrind --verbose --leak-check=full --show-reachable=yes $KROOT/client/test "$@"
else
  $KROOT/client/test "$@"
fi
