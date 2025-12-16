default_target: all

.PHONY: update_all clone_all coqutil clean_coqutil install_coqutil imp2lp all clean_imp2lp clean clean_deps clean_all install_imp2lp install

clone_all:
	git submodule update --init --recursive

update_all:
	git submodule update --recursive

REL_PATH_OF_THIS_MAKEFILE:=$(lastword $(MAKEFILE_LIST))
ABS_ROOT_DIR:=$(abspath $(dir $(REL_PATH_OF_THIS_MAKEFILE)))
# use cygpath -m because Coq on Windows cannot handle cygwin paths
ABS_ROOT_DIR:=$(shell cygpath -m '$(ABS_ROOT_DIR)' 2>/dev/null || echo '$(ABS_ROOT_DIR)')

COQUTIL_DIR ?= $(ABS_ROOT_DIR)/deps/coqutil/
export COQUTIL_DIR
SORTING_DIR ?= $(ABS_ROOT_DIR)/deps/coq-stdlib-edits/

coqutil:
	$(MAKE) -C $(COQUTIL_DIR)

clean_coqutil:
	$(MAKE) -C $(COQUTIL_DIR) clean

install_coqutil:
	$(MAKE) -C $(COQUTIL_DIR) install

sorting:
	$(MAKE) -C $(SORTING_DIR)

clean_sorting:
	$(MAKE) -C $(SORTING_DIR) clean

imp2lp: deps
	$(MAKE) -C $(ABS_ROOT_DIR)/imp2lp

clean_imp2lp:
	$(MAKE) -C $(ABS_ROOT_DIR)/imp2lp clean

install_imp2lp:
	$(MAKE) -C $(ABS_ROOT_DIR)/imp2lp install

deps: coqutil sorting

all: deps imp2lp

clean: clean_imp2lp

clean_deps: clean_coqutil clean_sorting

clean_all: clean_deps clean

install: install_coqutil install_imp2lp
