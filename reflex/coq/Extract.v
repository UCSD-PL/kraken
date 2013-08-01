Require Import Ynot.Extract.
Require Import ReflexEcho.
Require Import ReflexQuark.
Require Import ReflexSSH.
Require Import ReflexFdEcho.

Extraction Blacklist List String.

Extract Constant ReflexIO.exec     => "ReflexImpl.exec".
Extract Constant ReflexIO.call     => "ReflexImpl.call".
Extract Constant ReflexIO.select   => "ReflexImpl.select".
Extract Constant ReflexIO.recv     => "ReflexImpl.recv".
Extract Constant ReflexIO.send     => "ReflexImpl.send".
Extract Constant ReflexIO.recv_fd  => "ReflexImpl.recv_fd".
Extract Constant ReflexIO.send_fd  => "ReflexImpl.send_fd".
Extract Constant ReflexIO.oracle   => "ReflexImpl.oracle".

Cd "../ml".
Recursive Extraction Library ReflexEcho.
Recursive Extraction Library ReflexQuark.
Recursive Extraction Library ReflexSSH.
Recursive Extraction Library ReflexFdEcho.
