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

T=`date +"%y-%m-%d-%H:%M:%S"`
BENCHMARKS=benchmarks
GIT_BRANCH=$(parse_git_branch)$(parse_git_hash)
BASEOUTDIR=$BENCHMARKS/bench-opt-$GIT_BRANCH-$T
TIMEOUT=10h

function run_opt {
  git checkout Opt.v
  git diff-index --quiet HEAD
  if [ $? = 0 ];
  then
    rm -f Opt.v
    echo "Definition prune_pol := $1." > Opt.v
    echo "Definition prune_ni := $2." >> Opt.v
    echo "Definition rewrite_symb := $3." >> Opt.v
    echo "Definition ni_branch_prune := $4." >> Opt.v
    echo "Definition abstract_pf := $5." >> Opt.v
    echo "Definition abstract_pf_deep := $6." >> Opt.v
    OUTDIR=$BASEOUTDIR/${1:0:1}-${2:0:1}-${3:0:1}-${4:0:1}-${5:0:1}-${6:0:1}
    echo $OUTDIR
    mkdir $OUTDIR
    CONFIG=$OUTDIR/config.txt
    cat Opt.v > $CONFIG
    echo "Branch: $GIT_BRANCH" >> $CONFIG
    echo "Timeout: $TIMEOUT" >> $CONFIG
    SYSTEMSPEC=$BASEOUTDIR/sysspec.txt
    grep "model name" /proc/cpuinfo > $SYSTEMSPEC
    grep MemTotal /proc/meminfo >> $SYSTEMSPEC
    cat /proc/version >> $SYSTEMSPEC
    make bench BENCHOUT=$OUTDIR TIMEOUT=$TIMEOUT

#    (
#      CURRENTDIR=`pwd`
#      sed -e "s;%CSV%;$OUTDIR/results.csv;" $BENCHMARKS/template.tex > $OUTDIR/results.tex;
#      cd $OUTDIR
#      pdflatex results.tex
#      cd $CURRENTDIR
#    )

  else
    echo "Working directory dirty."
    echo "prune_pol:$1"
    echo "prune_ni:$2"
    echo "rewrite_symb:$3"
    echo "ni_branch_prune:$4"
    echo "abstract_pf:$5"
    echo "abstract_pf_deep:$6"
  fi
  git checkout Opt.v
}

mkdir $BASEOUTDIR
exec > $BASEOUTDIR/log.txt
while read i; do
  run_opt $i
done < $1
