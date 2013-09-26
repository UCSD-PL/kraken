include ../../Makefile.config

INCLUDES := -R $(YNOT) Ynot -I .
FILES    := $(filter-out Extract.v,$(wildcard *.v))

all:
	$(MAKE) depend
	$(MAKE) coq

bench:
	for i in `find . -name "bench-*"`; do make policies -C $$i; done

build:
	$(MAKE) depend
	$(MAKE) coq
	$(MAKE) build -C bench-$(NAME)

depend: $(FILES)
	$(COQDEP) $(INCLUDES) $^ > .depend

coq: $(FILES:.v=.vo)

%.vo: %.v
	$(COQC) $(INCLUDES) $*.v

clean:
	rm -f *.vo *.glob
	rm -f ../ml/*.vo ../ml/*.ml ../ml/*.mli
	for i in `find . -name "bench-*"`; do make clean -C $$i; done

include .depend

.PHONY: all depend coq clean
