include ../../Makefile.config

INCLUDES      := -R $(YNOT) Ynot -I .
BENCHINCLUDES := $(INCLUDES) -I ..
FILES         := $(filter-out Extract.v,$(wildcard *.v))
UBENCHKERNELS := $(wildcard ubench-*/Kernel.v)
BENCHKERNELS  := $(wildcard bench-*/Kernel.v)

all:
	$(MAKE) depend
	$(MAKE) coq
	$(MAKE) ubenchkernels
	$(MAKE) benchkernels

BENCHNAME := benchmark-$(shell date +"%y-%m-%d-%H:%M:%S")
BENCHDIR  := benchmarks
BENCHFULL := $(BENCHDIR)/$(BENCHNAME)

bench: all
	./bench.sh $(COQC) $(YNOT) bench $(BENCHOUT)

ubench: all
	./bench.sh $(COQC) $(YNOT) ubench $(BENCHOUT)

build:
	$(MAKE) depend
	$(MAKE) coq
	$(MAKE) build -C bench-$(NAME)

depend: $(FILES) $(BENCHKERNELS) $(UBENCHKERNELS)
	$(COQDEP) $(INCLUDES) $^ > .depend

coq: $(FILES:.v=.vo)
ubenchkernels: $(UBENCHKERNELS:.v=.vo)
benchkernels: $(BENCHKERNELS:.v=.vo)

%.vo: %.v
	$(COQC) $(INCLUDES) $*.v

clean:
	rm -f *.vo *.glob
	rm -f ../ml/*.vo ../ml/*.ml ../ml/*.mli
	for i in `find . -name "bench-*"`; do make clean -C $$i; done

include .depend

.PHONY: all depend coq clean bench ubench benchkernels ubenchkernels

