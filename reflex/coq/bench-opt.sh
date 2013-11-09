#!/bin/bash

function run_opt {
  rm -f Opt.v
  echo "Definition prune_pol := $1." > Opt.v
  echo "Definition prune_ni := $2." >> Opt.v
  echo "Definition rewrite_symb := $3." >> Opt.v
  echo "Definition ni_branch_prune := $4." >> Opt.v
  T=`date +"%y-%m-%d-%H:%M:%S"`
  OUT=bench-$T
  CONFIG=benchmarks/Opt-$T.v
  cp Opt.v $CONFIG
  echo $5 >> $CONFIG
  make bench BENCHOUT=$OUT
}

git diff-index --quiet HEAD
if [ $? = 0 ]; then
  run_opt false false false false
  run_opt true true false false
  run_opt true true true false
  run_opt true true true true
fi
