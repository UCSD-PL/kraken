Require Import Ynot.Extract.
Require Import Kernel.

Extraction Blacklist List String.

Extract Constant Message.chan     => "KrakenImpl.chan".
Extract Constant Message.tchan_eq => "KrakenImpl.tchan_eq".
Extract Constant Message.fdesc    => "KrakenImpl.fdesc".
Extract Constant Message.exec     => "KrakenImpl.exec".
Extract Constant Message.call     => "KrakenImpl.call".
Extract Constant Message.select   => "KrakenImpl.select".
Extract Constant Message.recv     => "KrakenImpl.recv".
Extract Constant Message.send     => "KrakenImpl.send".
Extract Constant Message.recv_fd  => "KrakenImpl.recv_fd".
Extract Constant Message.send_fd  => "KrakenImpl.send_fd".

Cd "../ml".
Recursive Extraction Library Kernel.
