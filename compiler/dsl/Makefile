all:
	$(MAKE) -C coq
	$(MAKE) -C c-stubs
	$(MAKE) -C ml

clean:
	$(MAKE) -C coq clean
	$(MAKE) -C c-stubs clean
	$(MAKE) -C ml clean

run: all
	ocamlrun -I c-stubs/ ml/_build/Main.byte

.PHONY: all clean run
