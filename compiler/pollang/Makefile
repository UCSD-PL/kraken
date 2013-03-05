include Makefile.config

INCLUDES := -R $(YNOT) Ynot -I . -I $(REFLEX)
FILES    := $(filter-out Extract.v,$(wildcard *.v))

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
	rm -f ../ml/*.vo ../ml/*.ml ../ml/*.mli

include .depend

.PHONY: all depend coq extract clean
