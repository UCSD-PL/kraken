include ../Makefile.config

CLIBS := $(wildcard $(KROOT)/c-stubs/*.c)
CLIBS := $(notdir $(basename $(CLIBS)))
CLIBS := $(patsubst %,-dllib\ -l%,$(CLIBS))

# TODO are all these -I -dllpath -dllib options necessary?
FLAGS := \
	-verbose 2 \
	-lib unix \
	-cflags -g,-I,$(KROOT)/c-stubs,-dllpath,$(KROOT)/c-stubs,$(CLIBS) \
	-lflags -g,-I,$(KROOT)/c-stubs,-dllpath,$(KROOT)/c-stubs,$(CLIBS) \
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
