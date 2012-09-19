YNOT          := ynot-20110710.tgz
YNOT_URL      := http://ynot.cs.harvard.edu/dist/ynot-20110710.tgz
PY_PASSFD     := kernel-template/client/python-passfd-0.2.tar.gz
PY_PASSFD_URL := http://python-passfd.googlecode.com/files/python-passfd-0.2.tar.gz

all: $(YNOT) $(PY_PASSFD)
	$(MAKE) -C src

clean:
	$(MAKE) -C src clean

dist-clean: clean
	rm -rf ynot $(YNOT) $(PY_PASSFD)

$(YNOT):
	wget -O $(YNOT) $(YNOT_URL)
	tar xvf $(YNOT)
	$(MAKE) -C ynot

$(PY_PASSFD):
	wget -O $(PY_PASSFD) $(PY_PASSFD_URL)

.PHONY: all clean dist-clean
