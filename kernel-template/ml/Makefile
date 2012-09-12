include ../Makefile.config

# commas and leading spaces cannot appear in the text of an argument
# define them as variables so we can use them in arguments
comma := ,
empty :=
space := $(empty) $(empty)

CLIBS := $(wildcard $(KROOT)/c-stubs/*.cma)
CLIBS := $(notdir $(CLIBS))
CLIBS := $(basename $(CLIBS))
CLIBS := $(subst $(space),$(comma),$(CLIBS))

FLAGS := \
	-libs unix,$(CLIBS) \
  -cflags -g,-I,$(KROOT)/c-stubs \
  -lflags -g,-I,$(KROOT)/c-stubs \
  -build-dir ../bin

all:
	mkdir -p ../bin
	cp primitives/* .
	$(OCAMLBUILD) $(FLAGS) Main.byte
	$(SLINK) ../bin/Main.byte ../bin/Main
  
clean:
	mkdir -p ../bin
	$(BUILD) $(FLAGS) -clean

.PHONY: all clean
