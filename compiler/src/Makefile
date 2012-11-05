OCAMLBUILD := ocamlbuild
OCB_FLAGS := \
	-lib str \
	-lib unix \
	-cflag -g \
	-lflag -g \
	-no-links

#ifneq "$(shell which menhir)" ""
	# would use --trace, but it ALWAYS prints to stderr :(
	# OCB_FLAGS := -use-menhir -yaccflags --explain,--trace $(OCB_FLAGS)
	OCB_FLAGS := -use-menhir -yaccflags --explain $(OCB_FLAGS)
#endif

SLINK := ln -s -f

all:
	$(OCAMLBUILD) $(OCB_FLAGS) kraken.byte
	$(SLINK) $(CURDIR)/_build/kraken.byte ../bin/.kraken
  
clean:
	$(OCAMLBUILD) $(OCB_FLAGS) -clean

.PHONY: all clean
