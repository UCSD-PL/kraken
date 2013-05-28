include ../Makefile.config

YNOT_URL      := http://ynot.cs.harvard.edu/dist/ynot-20110710.tgz
PY_PASSFD_URL := http://python-passfd.googlecode.com/files/python-passfd-0.2.tar.gz

all: ynot py-passfd

clean:
	rm -rf ynot.tgz ynot/
	rm -rf py-passfd.tgz py-passfd/

ynot:
	wget -O ynot.tgz $(YNOT_URL)
	tar xzf ynot.tgz
	$(MAKE) -C ynot

py-passfd:
	wget -O py-passfd.tgz $(PY_PASSFD_URL)
	tar xzf py-passfd.tgz
	mv python-passfd-0.2/ py-passfd/
	$(MAKE) -C py-passfd

.PHONY: all clean
