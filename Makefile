all:
	$(MAKE) -C ynot
	$(MAKE) -C src

clean:
	$(MAKE) -C src clean
	$(MAKE) -C ynot clean
