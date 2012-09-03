Require Import Ynot.Extract.
Require Import KrakenBase.
Require Import Kernel.

Extract Constant KrakenBase.chan  => "KrakenBaseImpl.chan".
Extract Constant KrakenBase.recvN => "KrakenBaseImpl.recvN".
Extract Constant KrakenBase.recvS => "KrakenBaseImpl.recvS".
Extract Constant KrakenBase.sendN => "KrakenBaseImpl.sendN".
Extract Constant KrakenBase.sendS => "KrakenBaseImpl.sendS".

Cd "../ml".
Recursive Extraction Library Kernel.
