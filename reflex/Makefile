all:
	touch coq/.depend
	$(MAKE) -C coq
	$(MAKE) -C c-stubs
	$(MAKE) -C ml

clean:
	$(MAKE) -C coq clean
	$(MAKE) -C c-stubs clean
	$(MAKE) -C ml clean

.PHONY: all clean
