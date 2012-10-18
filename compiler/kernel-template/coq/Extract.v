Require Import Ynot.Extract.
Require Import Kernel.

Extraction Blacklist List String.

Extract Constant Kernel.chan     => "KrakenImpl.chan".
Extract Constant Kernel.tchan_eq => "KrakenImpl.tchan_eq".
Extract Constant Kernel.fdesc    => "KrakenImpl.fdesc".
Extract Constant Kernel.exec     => "KrakenImpl.exec".
Extract Constant Kernel.call     => "KrakenImpl.call".
Extract Constant Kernel.select   => "KrakenImpl.select".
Extract Constant Kernel.recv     => "KrakenImpl.recv".
Extract Constant Kernel.send     => "KrakenImpl.send".
Extract Constant Kernel.recv_fd  => "KrakenImpl.recv_fd".
Extract Constant Kernel.send_fd  => "KrakenImpl.send_fd".

Cd "../ml".
Recursive Extraction Library Kernel.
