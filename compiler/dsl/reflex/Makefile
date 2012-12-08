include ../Makefile.config

INCLUDES := -R $(YNOT) Ynot -I .
FILES    := $(wildcard *.v)

all:
	$(MAKE) depend
	$(MAKE) coq

depend: $(FILES)
	$(COQDEP) $(INCLUDES) $^ > .depend

coq: $(FILES:.v=.vo)

%.vo: %.v
	$(COQC) $(INCLUDES) $*.v

clean:
	rm -f *.vo *.glob

include .depend

.PHONY: all depend coq clean
