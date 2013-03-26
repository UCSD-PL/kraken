include ../Makefile.config

SODIR := $(CURDIR)/../c-stubs
SOBJS := $(wildcard $(SODIR)/*.c)
SOBJS := $(notdir $(basename $(SOBJS)))
SOBJS := $(patsubst %,-dllib\ -l%,$(SOBJS))

FLAGS := \
	-verbose 2 \
	-lib unix \
	-cflags -g \
	-lflags -g,-I,$(SODIR),$(SOBJS) \
	-no-links

all:
	cp primitives/* .
	$(OCAMLBUILD) $(FLAGS) Main.byte
	cp _build/Main.byte kernel
	$(OCAMLBUILD) $(FLAGS) SSHMain.byte
	cp _build/SSHMain.byte ssh_kernel
  
clean:
	$(OCAMLBUILD) $(FLAGS) -clean
	rm -f kernel

.PHONY: all clean
