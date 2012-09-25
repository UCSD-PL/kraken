#!/usr/bin/env bash

function error {
  echo ERROR : $*
  exit 1
}

if [ ! -f $KRAKEN/.kraken-root ]; then
  error "\$KRAKEN must point to root of Kraken repository."
fi

TEST=$KRAKEN/compiler/test
KBIN=$KRAKEN/compiler/bin

PASS=$'\033[1;32mPASS\033[0m'
FAIL=$'\033[1;31mFAIL\033[0m'

D=$(mktemp -d /tmp/kraken-test-XXXXXX)

echo "Output written to $D"

date > $D/timestamp.txt

for t in $TEST/*.krn; do
  NAME=$(basename $t .krn)
  LOG=$D/$NAME-log
  printf "%-15s" $NAME
  $KBIN/kraken.sh $t -o $D --build > $LOG 2>&1
  if [ $? -eq 0 ]; then
    echo $PASS
  else
    echo $FAIL
  fi
done
