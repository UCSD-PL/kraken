BUILD = ocamlbuild
SLINK = ln -s -f

FLAGS = \
  -libs unix,str \
  -cflag -g \
  -lflag -g \
  -build-dir ../bin

all:
	mkdir -p ../bin
	$(BUILD) $(FLAGS) kraken.byte
	$(SLINK) ../bin/kraken.byte ../bin/kraken
  
clean:
	$(BUILD) $(FLAGS) -clean
