#!/bin/bash

if [ $# -ne 4 ]
then echo "Usage: bench COQC YNOT PREFIX"; exit 65
fi

COQC=$1
YNOT=$2
PREFIX=$3
BENCHINCLUDES="-R $YNOT Ynot -I . -I .."
BENCHNAME=$4
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
    tmp=`mktemp`;
    timeout 5s $COQC $BENCHINCLUDES $b &> "$tmp" &
    timeoutpid=$!
    coqpid=`pidof coqtop.opt`;
    while [[ -z $coqpid ]]; do
        sleep 0.1;
	coqpid=`pidof coqtop.opt`
    done;
    peak=0;
    while ps -p $coqpid > /dev/null; do
      sleep 0.2
      sample=`ps -o rss= $coqpid 2>&1`
      if [[ "$sample" -gt "$peak" ]]; then
          peak=$sample
      fi
    done
    wait $timeoutpid
    status=$?;
    coqres=$(<$tmp) && rm $tmp
    coqtime=`echo -n "$coqres"\
      | grep "Finished transaction"\
      | sed -r 's/Finished transaction in (.*)\. secs.*/\1/'\
      | paste -sd ","
      `;
    if [[ "$status" = "124" ]];
    then echo "Timeout,,$peak" >> ../$BENCHFULL.csv;
    else
      if [[ "$status" = "0" ]];
      then
        if [[ -z "$coqtime" ]];
        then
          echo -n $coqres\
            | tr -d '"'\
            | sed -e 's/_/\\_/'\
            | sed -r 's/(.*)/{\1}/' >> ../$BENCHFULL.csv;
        else echo -n $coqtime >> ../$BENCHFULL.csv;
        fi;
        echo ,$peak >> ../$BENCHFULL.csv;
      else
        echo "Error with status code: $status,,$peak" >> ../$BENCHFULL.csv;
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

