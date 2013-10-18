#!/bin/bash

if [ $# -ne 3 ]
then echo "Usage: bench COQC YNOT PREFIX"; exit 65
fi

COQC=$1
YNOT=$2
PREFIX=$3
BENCHINCLUDES="-R $YNOT Ynot -I . -I .."
BENCHNAME=$PREFIX-`date +"%y-%m-%d-%H:%M:%S"`
BENCHDIR=benchmarks
BENCHFULL=$BENCHDIR/$BENCHNAME

echo "Benchmark,Policy,Time" >> $BENCHFULL.csv

for d in `ls -d -- $PREFIX-*`;
do (
  echo `basename $d`;
  cd $d;
  $COQC $BENCHINCLUDES Kernel.v;
  for b in `find . -name "Policy*.v"`;
  do (
    echo `basename $b .v`;
    echo -n `basename $d`,    | sed -e "s/^$PREFIX-//" >> ../$BENCHFULL.csv;
    echo -n `basename $b .v`, | sed -e "s/^Policy//"   >> ../$BENCHFULL.csv;
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
      then
        echo $coqres\
          | tr -d '"'\
          | sed -e 's/_/\\_/'\
          | sed -r 's/(.*)/{\1}/' >> ../$BENCHFULL.csv;
      else echo {$coqtime} >> ../$BENCHFULL.csv;
      fi;
    fi;
  );
  done;
);
done

(
  cd $BENCHDIR;
  sed -e "s;%CSV%;$BENCHNAME.csv;" template.tex > $BENCHNAME.tex;
  pdflatex $BENCHNAME.tex
)

