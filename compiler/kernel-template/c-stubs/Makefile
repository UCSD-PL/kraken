include ../Makefile.config

FILES := $(wildcard *.c)

all: $(FILES:.c=.cma)

%.cma: %.c
	$(CC) -I $(OCAMLH) -c $*.c
	$(AR) rcs lib$*.a $*.o
	$(OCAMLC) -a -o $*.cma -custom -cclib -l$*
 
clean:
	rm -f *.cma *.a *.o

.PHONY: all clean
