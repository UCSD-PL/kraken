all:
	$(MAKE) -C coq
	$(MAKE) -C c-stubs
	$(MAKE) -C ml
	$(MAKE) -C client

clean:
	# clean in reverse order
	$(MAKE) -C client clean
	$(MAKE) -C ml clean
	$(MAKE) -C c-stubs clean
	$(MAKE) -C coq clean

.PHONY: all clean
