default_target: all

.PHONY: update_all clone_all datalog clean_datalog imp2lp all clean_imp2lp clean clean_deps clean_all install_imp2lp install

clone_all:
	git submodule update --init --recursive

update_all:
	git submodule update --recursive

REL_PATH_OF_THIS_MAKEFILE:=$(lastword $(MAKEFILE_LIST))
ABS_ROOT_DIR:=$(abspath $(dir $(REL_PATH_OF_THIS_MAKEFILE)))
# use cygpath -m because Coq on Windows cannot handle cygwin paths
ABS_ROOT_DIR:=$(shell cygpath -m '$(ABS_ROOT_DIR)' 2>/dev/null || echo '$(ABS_ROOT_DIR)')

SORTING_DIR ?= $(ABS_ROOT_DIR)/deps/coq-stdlib-edits/
DATALOG_DIR ?= $(ABS_ROOT_DIR)/deps/datalog/

sorting:
	$(MAKE) -C $(SORTING_DIR)

clean_sorting:
	$(MAKE) -C $(SORTING_DIR) clean

datalog:
	dune build --root $(DATALOG_DIR)

clean_datalog:
	dune clean --root $(DATALOG_DIR)

imp2lp: deps
	$(MAKE) -C $(ABS_ROOT_DIR)/imp2lp

clean_imp2lp:
	$(MAKE) -C $(ABS_ROOT_DIR)/imp2lp clean

install_imp2lp:
	$(MAKE) -C $(ABS_ROOT_DIR)/imp2lp install

deps: sorting datalog

all: deps imp2lp

clean: clean_imp2lp

clean_deps: clean_sorting clean_datalog

clean_all: clean_deps clean

install: install_imp2lp
