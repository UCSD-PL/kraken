include ../Makefile.config

all: passfd

passfd:
	tar xzf python-passfd-0.2.tar.gz
	cd python-passfd-0.2 \
		&& ./setup.py build --verbose &> passfd-build-log \
		&& ./setup.py install --verbose --prefix "$(KROOT)" &> passfd-install-log

clean:
	# only removes temporary build files, not installed passfd
	cd python-passfd-0.2 \
		&& ./setup.py clean

.PHONY: all passfd clean
