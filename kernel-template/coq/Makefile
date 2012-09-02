INCLUDES := -I $(KRAKEN)/ynot/src/coq -I .
COQC     := coqc $(INCLUDES)
COQDEP   := coqdep $(INCLUDES)
FILES    := $(filter-out Extract.v, $(wildcard *.v))

include .depend

all:
	$(MAKE) depend
	$(MAKE) coq
	$(MAKE) extract

depend: $(FILES)
	$(COQDEP) $^ > .depend

coq: $(FILES:.v=.vo)

%.vo: %.v
	$(COQC) $*.v

extract: Extract.vo

clean:
	rm -f *.vo *.glob
	rm -f ../ml/*.vo ../ml/*.ml ../ml/*.mli
