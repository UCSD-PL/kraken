include ../../Makefile.config

INCLUDES := -R $(YNOT) Ynot -I .
FILES    := $(filter-out Extract.v,$(wildcard *.v))

all:
	$(MAKE) depend
	$(MAKE) coq
	$(MAKE) extract

bench:
	for i in `find . -name "bench-*"`; do make policies -C $$i; done

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
