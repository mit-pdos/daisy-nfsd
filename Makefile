DFY_FILES := $(shell find src -name "*.dfy")
OK_FILES := $(DFY_FILES:.dfy=.dfy.ok)

# these arguments don't affect verification outcomes
DAFNY_LOAD := 0.5
DAFNY_BASIC_ARGS = /compile:0 /compileTarget:go /timeLimit:20 /vcsLoad:$(DAFNY_LOAD)
DAFNY_ARGS := /noNLarith /arith:5
DAFNY=./etc/dafnyq $(DAFNY_BASIC_ARGS) $(DAFNY_ARGS)

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
src/Dafny/nonlin/%.dfy.ok: DAFNY_ARGS = /arith:1

# these proofs are slow and prone to timeouts
src/Dafny/examples/fs/dir_fs.dfy.ok: DAFNY_LOAD = 0.2

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
dafnygen/dafnygen.go: src/Dafny/compile.dfy $(DFY_FILES)
	@echo "DAFNY COMPILE $<"
	$(Q)$(DAFNY) /countVerificationErrors:0 /spillTargetCode:2 /out dafnygen $<
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
