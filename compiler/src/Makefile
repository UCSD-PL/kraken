BUILD := ocamlbuild
SLINK := ln -s -f

FLAGS = \
	-lib unix \
	-cflag -g \
	-lflag -g \
	-no-links

all:
	$(BUILD) $(FLAGS) kraken.byte
	$(SLINK) $(CURDIR)/_build/kraken.byte ../bin/kraken
  
clean:
	$(BUILD) $(FLAGS) -clean

.PHONY: all clean
