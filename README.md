# Reflex DSL: Automating Formal Proofs for Reactive Systems

This repository gives the source code for the project described at this page: http://goto.ucsd.edu/reflex/. A VM image is available at that web page for trying out the systems we built (web browser, SSH server, web server), running the proof automation, and building a kernel of your own using Reflex.

This document describes the structure of this repository.

## Directory structure

The important parts of the repository are the following:

* The implementation of the interpreter is located at `reflex/coq`. A description of some of the files under that directory is given at `docs/source-docs.txt`.

* The kernels for the web browser, ssh server, and web server are located at `reflex/coq/bench-quark/Kernel.reflex`, `reflex/coq/bench-ssh/Kernel.reflex`, `reflex/coq/bench-webserver/Kernel.reflex`, respectively.

* The implementation of the proof automation is also found in `reflex/coq`. The bulk of the implementation is, somewhat confusingly, in the file `ReflexFrontend.v`.

## Compiling

Simply run `make` to build the interpreter. In order to build a particular kernel, place your kernel in `reflex/coq/bench-<name>`. Under that directory, run

```ln -s ../Makefile.bench Makefile
cd ../../
`make build NAME=<name>
```

The resulting binary will reside in `reflex/coq/bench-<name>/ml/kernel`.

## Running the proof automation on our properties
`cd reflex/coq`
`make bench BENCHOUT=<results-dir> TIMEOUT=<timeout>`

A single file called <results-dir>/results.csv will be created, giving, for each property, the time taken to produce a proof (Ltac), the time taken to check the proof (Qed), and the maximum memory used while creating the proof.

You can also tweak the automation optimizations that are run by modifying Opt.v. This file consists of six boolean valued expressions, each corresponding to an optimization.

Make sure that when you run automation on a machine with at least 4GB of memory.

## Running the proof automation on your properties
Enter the directory where the kernel resides. Run `make policies`.
