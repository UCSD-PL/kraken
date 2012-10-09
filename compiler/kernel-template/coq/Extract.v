Require Import Ynot.Extract.
Require Import Kraken.
Require Import Kernel.

Extraction Blacklist List String.

Extract Constant Kraken.chan     => "KrakenImpl.chan".
Extract Constant Kraken.tchan_eq => "KrakenImpl.tchan_eq".
Extract Constant Kraken.fdesc    => "KrakenImpl.fdesc".
Extract Constant Kraken.exec     => "KrakenImpl.exec".
Extract Constant Kraken.call     => "KrakenImpl.call".
Extract Constant Kraken.select   => "KrakenImpl.select".
Extract Constant Kraken.recv     => "KrakenImpl.recv".
Extract Constant Kraken.send     => "KrakenImpl.send".
Extract Constant Kraken.recv_fd  => "KrakenImpl.recv_fd".
Extract Constant Kraken.send_fd  => "KrakenImpl.send_fd".

Cd "../ml".
Recursive Extraction Library Kernel.
