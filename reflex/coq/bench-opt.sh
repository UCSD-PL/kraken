#!/bin/bash

# checks if branch has something pending
function parse_git_dirty() {
  git diff --quiet --ignore-submodules HEAD 2>/dev/null; [ $? -eq 1 ] && echo "*"
}

# gets the current git branch
function parse_git_branch() {
  git branch --no-color 2> /dev/null | sed -e '/^[^*]/d' -e "s/* \(.*\)/\1$(parse_git_dirty)/"
}
 
# get last commit hash prepended with @ (i.e. @8a323d0)
function parse_git_hash() {
  git rev-parse --short HEAD 2> /dev/null | sed "s/\(.*\)/@\1/"
}

function run_opt {
  rm -f Opt.v
  echo "Definition prune_pol := $1." > Opt.v
  echo "Definition prune_ni := $2." >> Opt.v
  echo "Definition rewrite_symb := $3." >> Opt.v
  echo "Definition ni_branch_prune := $4." >> Opt.v
  T=`date +"%y-%m-%d-%H:%M:%S"`
  GIT_BRANCH=$(parse_git_branch)$(parse_git_hash)
  OUT=bench-$T-$GIT_BRANCH
  CONFIG=benchmarks/Opt-$OUT.v
  cp Opt.v $CONFIG

}

git diff-index --quiet HEAD
if [ $? = 0 ]; then
  run_opt false false false false
  run_opt true true false false
  run_opt true true true false
  run_opt true true true true
fi
