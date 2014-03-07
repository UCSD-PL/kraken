#!/bin/bash

# insert user-defined primitives into the Reflex runtime module
# if a benchmark has UserPrimitives.ml file.

TEMPLATE=./ml/primitives/ReflexImpl.ml
if [ -a UserPrimitives.ml ];
then
    start=`grep -n "(\* BEGIN:UserPrimitives \*)" $TEMPLATE | cut -f1 -d:`
    end=`grep -n "(\* END:UserPrimitives \*)" $TEMPLATE | cut -f1 -d:`
    lineno=`wc $TEMPLATE | cut -f2 -d' '`
    tempfile=`mktemp`
    head -n $start $TEMPLATE > tempfile
    cat UserPrimitives.ml >> tempfile
    tail -n $(($lineno-$(($end-1)))) $TEMPLATE >> tempfile
    mv tempfile $TEMPLATE
fi