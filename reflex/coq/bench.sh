#!/bin/bash

if [ $# -ne 2 ]
then echo "Usage: bench COQC YNOT"; exit 65
fi;

COQC=$1
YNOT=$2
BENCHINCLUDES="-R $YNOT Ynot -I . -I .."
BENCHNAME=benchmark-`date +"%y-%m-%d-%H:%M:%S"`
BENCHDIR=benchmarks
BENCHFULL=$BENCHDIR/$BENCHNAME

echo "Benchmark,Policy,Time" >> $BENCHFULL.csv

for d in `find . -name "bench-*"`;
do (
  echo `basename $d`;
  cd $d;
  $COQC $BENCHINCLUDES Kernel.v;
  for b in `find . -name "Policy*.v"`;
  do (
    echo `basename $b .v`;
    echo -n `basename $d`,`basename $b .v`, >> ../$BENCHFULL.csv;
    coqres=`timeout --foreground 1h $COQC $BENCHINCLUDES $b 2>&1`;
    status=$?;
    coqtime=`echo "$coqres" \
      | grep "Finished transaction" \
      | sed -r 's/Finished transaction in (.*)/\1/'
      `;
    if [[ "$status" = "124" ]];
    then echo "Timeout" >> ../$BENCHFULL.csv;
    else
      if [[ -z "$coqtime" ]];
      then echo $coqres | tr -d '"' | sed -r 's/(.*)/{\1}/' >> ../$BENCHFULL.csv;
      else echo {$coqtime} >> ../$BENCHFULL.csv;
      fi;
    fi;
  );
  done;
);
done;

(
  cd $BENCHDIR;
  sed -e "s;%CSV%;$BENCHNAME.csv;" template.tex > $BENCHNAME.tex;
  pdflatex $BENCHNAME.tex
)

