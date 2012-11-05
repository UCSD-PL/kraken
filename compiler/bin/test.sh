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
rm -f    /tmp/kraken-test-last
ln -s $D /tmp/kraken-test-last

echo "Output written to $D (symlinked /tmp/kraken-test-last)"

date > $D/timestamp.txt

T0=$(date +%s)
for t in $TEST/*; do
  NAME=$(basename $t)
  LOG=$D/$NAME-log
  printf "%-20s" $NAME
  t0=$(date +%s)
  $KBIN/kraken.sh $t --outdir $D --build > $LOG 2>&1
  if [ $? -eq 0 ]; then
    echo -n $PASS
  else
    echo -n $FAIL
  fi
  tn=$(date +%s)
  printf "%4s%3d\n" "" $(($tn - $t0))
done
TN=$(date +%s)
printf "\nTotal time : %3d\n" $(($TN - $T0))
