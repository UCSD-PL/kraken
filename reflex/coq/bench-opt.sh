#!/bin/bash

# checks if branch has something pending
function parse_git_dirty() {
  git diff --quiet --ignore-submodules HEAD 2>/dev/null; [ $? -eq 1 ] && echo "*"
}

# gets the current git branch
function parse_git_branch() {
  git branch --no-color 2> /dev/null | sed -e '/^[^*]/d' -e "s/* \(.*\)/\1/"
}
 
# get last commit hash prepended with @ (i.e. @8a323d0)
function parse_git_hash() {
  git rev-parse --short HEAD 2> /dev/null | sed "s/\(.*\)/@\1/"
}

function run_opt {
  GIT_BRANCH=$(parse_git_branch)$(parse_git_hash)
  rm -f Opt.v
  echo "Definition prune_pol := $1." > Opt.v
  echo "Definition prune_ni := $2." >> Opt.v
  echo "Definition rewrite_symb := $3." >> Opt.v
  echo "Definition ni_branch_prune := $4." >> Opt.v
  echo "Definition ni_branch_prune := $5." >> Opt.v
  OUT=bench-$GIT_BRANCH-$6
  CONFIG=benchmarks/Opt-$OUT.v
  cp Opt.v $CONFIG
  make bench BENCHOUT=$OUT
}

git diff-index --quiet HEAD
if [ $? = 0 ]; then
  run_opt false false false false false 1
  run_opt true true false false false 2
  run_opt true true true false false 3
  run_opt true true true true false 4
  run_opt true true true true true 5
fi
