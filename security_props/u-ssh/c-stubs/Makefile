include ../Makefile.config

FILES := $(wildcard *.c)

all: $(FILES:.c=.so)

%.so: %.c
	$(CC) -I $(OCAMLH) -fpic -c $*.c
	$(CC) -shared -Wl,-soname,lib$*.so -o dll$*.so $*.o

clean:
	rm -f *.o *.so

.PHONY: all clean
