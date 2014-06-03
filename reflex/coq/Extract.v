Require Import Ynot.Extract.
Require Import Kernel.

Extraction Blacklist List String.

Extract Constant ReflexIO.exec     => "ReflexImpl.exec".
Extract Constant ReflexIO.call     => "ReflexImpl.call".
Extract Constant ReflexIO.select   => "ReflexImpl.select".
Extract Constant ReflexIO.recv     => "ReflexImpl.recv".
Extract Constant ReflexIO.send     => "ReflexImpl.send".
Extract Constant ReflexIO.recv_fd  => "ReflexImpl.recv_fd".
Extract Constant ReflexIO.send_fd  => "ReflexImpl.send_fd".

Extract Constant ReflexIO.invoke_fd  => "ReflexImpl.invoke_fd".
Extract Constant ReflexIO.invoke_str => "ReflexImpl.invoke_str".

Cd "ml/".
Recursive Extraction Library Kernel.
