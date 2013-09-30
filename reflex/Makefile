all:
	touch coq/.depend
	$(MAKE) -C coq
	$(MAKE) -C c-stubs

build:
	touch coq/.depend
	$(MAKE) -C c-stubs
	$(MAKE) build -C coq NAME=$(NAME)

clean:
	$(MAKE) -C coq clean
	$(MAKE) -C c-stubs clean
	$(MAKE) -C ml clean

.PHONY: all clean
