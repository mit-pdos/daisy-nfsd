DFY_FILES := $(shell find src -name "*.dfy")
OK_FILES := $(DFY_FILES:.dfy=.dfy.ok)

DAFNY_CORES := "50%"

# these arguments don't affect verification outcomes
DAFNY_BASIC_ARGS := --verification-time-limit 20 --cores $(DAFNY_CORES)

DAFNY_ARGS := --disable-nonlinear-arithmetic
DAFNY = ./etc/dafnyq verify $(DAFNY_BASIC_ARGS) $(DAFNY_ARGS)

Q:=@

default: all

compile: dafnygen/dafnygen.go

verify: $(OK_FILES)

all: verify compile

.dafnydeps.d: $(DFY_FILES) etc/dafnydep
	@echo "DAFNYDEP"
	$(Q)./etc/dafnydep $(DFY_FILES) > $@

# do not try to build dependencies if cleaning
ifeq ($(filter clean,$(MAKECMDGOALS)),)
-include .dafnydeps.d
endif

# allow non-linear reasoning for nonlin directory specifically
src/nonlin/%.dfy.ok: DAFNY_ARGS =

%.dfy.ok: %.dfy
	@echo "DAFNY $<"
	$(Q)$(DAFNY) "$<"
	$(Q)touch "$@"

# Compilation produces output in dafnygen-go, which we preprocess with
# dafnygen-imports.py to change import paths (for go module compatibility) and
# to place the output under dafnygen without a src directory.
#
# We then run gofmt to simplify the code for readability and goimports to clean
# up unused imports emitted by Dafny.
dafnygen/dafnygen.go: src/compile.dfy $(DFY_FILES)
	@echo "DAFNY COMPILE $<"
	# TODO: use dafny translate (new CLI)
	$(Q)./etc/dafnyq /compileTarget:go /noVerify /spillTargetCode:2 /out dafnygen $<
	$(Q)rm -rf dafnygen
	$(Q)cd dafnygen-go/src && ../../etc/dafnygen-imports.py ../../dafnygen
	$(Q)rm -r dafnygen-go
	$(Q)gofmt -w -r '(a) -> a' ./dafnygen
	$(Q)goimports -w ./dafnygen

clean:
	@echo "CLEAN"
	$(Q)find . -name "*.dfy.ok" -delete
	$(Q)rm -f .dafnydeps.d
	$(Q)rm -rf dafnygen
	$(Q)rm -f daisy-nfsd cpu.prof mem.prof nfs.out
