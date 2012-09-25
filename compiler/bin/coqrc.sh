#!/usr/bin/env bash

function error {
  echo ERROR : $*
  exit 1
}

if [ ! -f $KRAKEN/.kraken-root ]; then
  error "\$KRAKEN must point to root of Kraken repository."
fi

cat > ~/.coqrc <<EOF
Add LoadPath "$KRAKEN/compiler/ynot/src/coq" as Ynot.
Add LoadPath "$KRAKEN/compiler/ynot/examples/IO" as IO.
Add LoadPath "$KRAKEN/compiler/ynot/examples/servers".
EOF
