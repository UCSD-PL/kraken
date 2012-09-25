#!/usr/bin/env bash

export KROOT="__KROOT__"
export PYTHONPATH="$PYTHONPATH:$KROOT/lib/python2.7/site-packages"

$KROOT/bin/.Main
