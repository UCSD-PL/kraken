#!/usr/bin/env bash

cat > ~/.coqrc <<EOF
Add LoadPath "$PWD/ynot/src/coq" as Ynot.
Add LoadPath "$PWD/ynot/examples/IO" as IO.
Add LoadPath "$PWD/ynot/examples/servers".
EOF
