BUILD = ocamlbuild
SLINK = ln -s -f

FLAGS = \
  -libs unix,str \
  -cflag -g \
  -lflag -g \
  -build-dir ../bin

all:
	mkdir -p ../bin
	cp primitives/* .
	$(BUILD) $(FLAGS) Main.byte
	$(SLINK) ../bin/Main.byte ../bin/Main
  
clean:
	mkdir -p ../bin
	$(BUILD) $(FLAGS) -clean
