SRC = src
TEST = t
BUILDDIR = build
DISTDIR = dist

# Gah
SUBBUILDDIR = $(shell python -c 'import distutils.util, sys; print "lib.%s-%s" % (distutils.util.get_platform(), sys.version[0:3])')
BUILDDIR := $(BUILDDIR)/$(SUBBUILDDIR)

COVERAGE = $(or $(shell which coverage), $(shell which python-coverage), \
	   coverage)

all:
	./setup.py build

install: all
	./setup.py install

test: all
	retval=0; \
	for i in `find "$(TEST)" -perm -u+x -type f`; do \
		echo $$i; \
		PYTHONPATH="$(BUILDDIR):$$PYTHONPATH" $$i || retval=$$?; \
		done; exit $$retval

coverage: all
	rm -f .coverage
	for i in `find "$(TEST)" -perm -u+x -type f`; do \
		set -e; \
		PYTHONPATH="$(BUILDDIR):$$PYTHONPATH" $(COVERAGE) -x $$i; \
		done
	$(COVERAGE) -r -m `find "$(BUILDDIR)" -name \\*.py -type f`
	rm -f .coverage

clean:
	./setup.py clean
	rm -f `find -name \*.pyc` .coverage

distclean: clean
	rm -rf "$(DISTDIR)"

dist:
	./setup.py sdist

.PHONY: clean distclean dist test coverage install
