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
	$(BUILD) $(FLAGS) Kernel.byte
	$(SLINK) ../bin/Kernel.byte ../bin/Kernel
  
clean:
	mkdir -p ../bin
	$(BUILD) $(FLAGS) -clean
