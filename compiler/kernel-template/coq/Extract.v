Require Import Ynot.Extract.
Require Import KrakenBase.
Require Import Kernel.

Extract Constant KrakenBase.chan => "KrakenBaseImpl.chan".
Extract Constant KrakenBase.fdesc => "KrakenBaseImpl.fdesc".
Extract Constant KrakenBase.exec => "KrakenBaseImpl.exec".
Extract Constant KrakenBase.call => "KrakenBaseImpl.call".
Extract Constant KrakenBase.recv => "KrakenBaseImpl.recv".
Extract Constant KrakenBase.send => "KrakenBaseImpl.send".
Extract Constant KrakenBase.recv_fd => "KrakenBaseImpl.recv_fd".
Extract Constant KrakenBase.send_fd => "KrakenBaseImpl.send_fd".

Extract Constant Kernel.dummy => "KrakenBaseImpl.mkchan ()".

Cd "../ml".
Recursive Extraction Library Kernel.
