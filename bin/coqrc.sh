#!/usr/bin/env bash

if [ ! -f $KRAKEN/.kraken-root ]; then
  error "\$KRAKEN must point to root of Kraken repository."
fi

cat > ~/.coqrc <<EOF
Add LoadPath "$KRAKEN/ynot/src/coq" as Ynot.
Add LoadPath "$KRAKEN/ynot/examples/IO" as IO.
Add LoadPath "$KRAKEN/ynot/examples/servers".
EOF
