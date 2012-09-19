include ../Makefile.config

# TODO make ynot path part of Makefile.config
INCLUDES := -I $(KRAKEN)/ynot/src/coq -I .
FILES    := $(filter-out Extract.v,$(wildcard *.v))

all:
	$(MAKE) depend
	$(MAKE) coq
	$(MAKE) extract

depend: $(FILES)
	$(COQDEP) $(INCLUDES) $^ > .depend

coq: $(FILES:.v=.vo)

%.vo: %.v
	$(COQC) $(INCLUDES) $*.v

extract: Extract.vo

clean:
	rm -f *.vo *.glob
	rm -f ../ml/*.vo ../ml/*.ml ../ml/*.mli

include .depend

.PHONY: all depend coq extract clean
