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

echo "Benchmark,Policy,Time (Ltac),Time (Qed)" >> $BENCHFULL.csv

for d in `ls -d -- $PREFIX-*`;
do (
  echo `basename $d`;
  cd $d;
  $COQC $BENCHINCLUDES Kernel.v;
  for b in `find . -name "Policy*.v"`;
  do (
    policy=`basename $b .v`;
    echo $policy;
    echo -n `basename $d`,    | sed -e "s/^$PREFIX-//" >> ../$BENCHFULL.csv;
    echo -n `basename $b .v`\
      | sed -e "s/^Policy//"\
      | ../benchnames.py >> ../$BENCHFULL.csv;
    echo -n , >> ../$BENCHFULL.csv;
    coqres=`timeout --foreground 1h $COQC $BENCHINCLUDES $b 2>&1`;
    status=$?;
    coqtime=`echo -n "$coqres"\
      | grep "Finished transaction"\
      | sed -r 's/Finished transaction in (.*)\. secs.*/\1/'\
      | paste -sd ","
      `;
    if [[ "$status" = "124" ]];
    then echo "Timeout" >> ../$BENCHFULL.csv;
    else
      if [[ "$status" = "0" ]];
      then
        if [[ -z "$coqtime" ]];
        then
          echo $coqres\
            | tr -d '"'\
            | sed -e 's/_/\\_/'\
            | sed -r 's/(.*)/{\1}/' >> ../$BENCHFULL.csv;
        else echo $coqtime >> ../$BENCHFULL.csv;
        fi;
      else
        echo "Error with status code: $status" >> ../$BENCHFULL.csv;
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

