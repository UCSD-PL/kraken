include ../Makefile.config

CLIBS := $(wildcard $(KROOT)/c-stubs/*.cma)
CLIBS := $(notdir $(basename $(CLIBS)))
CLIBS := $(patsubst %,-lib %,$(CLIBS))

FLAGS := \
  -lib unix \
  $(CLIBS) \
  -cflags -g,-I,$(KROOT)/c-stubs \
  -lflags -g,-I,$(KROOT)/c-stubs \
	-no-links

all:
	mkdir -p ../bin
	cp primitives/* .
	$(OCAMLBUILD) $(FLAGS) Main.byte
	$(SLINK) $(CURDIR)/_build/Main.byte ../bin/.Main
  
clean:
	mkdir -p ../bin
	$(OCAMLBUILD) $(FLAGS) -clean

.PHONY: all clean
