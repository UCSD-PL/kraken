include Makefile.config

all:
	$(MAKE) -C dep
	$(MAKE) -C reflex
	$(MAKE) -C examples

depclean:
	$(MAKE) -C dep clean

clean:
	$(MAKE) -C reflex clean
	$(MAKE) -C examples clean

.PHONY: all depclean clean
