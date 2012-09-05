Require Import Ynot.Extract.
Require Import KrakenBase.
Require Import Kernel.

Extract Constant KrakenBase.chan => "KrakenBaseImpl.chan".
Extract Constant KrakenBase.recv => "KrakenBaseImpl.recv".
Extract Constant KrakenBase.send => "KrakenBaseImpl.send".

Extract Constant Kernel.c => "KrakenBaseImpl.mkchan ()".

Cd "../ml".
Recursive Extraction Library Kernel.
