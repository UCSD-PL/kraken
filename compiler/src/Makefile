OCAMLBUILD := ocamlbuild
OCB_FLAGS := \
	-lib str \
	-lib unix \
	-cflag -g \
	-lflag -g \
	-no-links

SLINK := ln -s -f

all:
	$(OCAMLBUILD) $(OCB_FLAGS) kraken.byte
	$(SLINK) $(CURDIR)/_build/kraken.byte ../bin/.kraken
  
clean:
	$(OCAMLBUILD) $(OCB_FLAGS) -clean

.PHONY: all clean
