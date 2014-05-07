#!/bin/bash
echo "$QUARK_CROOT/input/input.sh"
echo $1
#xterm -title "Quark Web Browser Address Bar" -geometry 110x5+100+155 -fn *-fixed-*-*-*-20-* -e $QUARK_CROOT/input/input.sh $1
xterm -title "Quark Web Browser Address Bar" -geometry 110x4+63+0 -fn *-fixed-*-*-*-20-* -e $QUARK_CROOT/input/input.sh $1
