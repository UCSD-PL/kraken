include ../../Makefile.config

INCLUDES := -R $(YNOT) Ynot -I .
FILES    := $(filter-out Extract.v EnablesTest.v NIHelperFacts.v, $(wildcard *.v))

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
