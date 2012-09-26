include ../Makefile.config

all: passfd

passfd:
	tar xzf python-passfd-0.2.tar.gz
	cd python-passfd-0.2 \
		&& patch < ../passfd-2.7.patch \
		&& ./setup.py build --verbose \
		&& ./setup.py install --verbose --prefix "$(KROOT)"

clean:
	# only removes temporary build files, not installed passfd
	cd python-passfd-0.2 \
		&& ./setup.py clean

.PHONY: all passfd clean
