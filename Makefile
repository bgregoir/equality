# -*- Makefile -*-

# --------------------------------------------------------------------
SUBDIRS :=

include Makefile.common

# --------------------------------------------------------------------
.PHONY: install extraction

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

# --------------------------------------------------------------------
this-clean::
	rm -f src/*.glob src/*.d src/*.vo src/.*.vo

this-distclean::
	rm -f $(shell find . -name '*~')
