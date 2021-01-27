DFY_FILES := $(shell find src -name "*.dfy")
OK_FILES := $(DFY_FILES:.dfy=.dfy.ok)

DAFNY_ARGS := /compile:0 /compileTarget:go /z3opt:smt.arith.nl=false /arith:5 /timeLimit:40 /vcsLoad:0.5
DAFNY=./etc/dafnyq $(DAFNY_ARGS)

Q:=@

default: $(OK_FILES)

compile: bank-go/src/bank.go

all: $(OK_FILES) compile

.dafnydeps.d: $(DFY_FILES) etc/dafnydep
	@echo "DAFNYDEP"
	$(Q)./etc/dafnydep $(DFY_FILES) > $@

# do not try to build dependencies if cleaning
ifeq ($(filter clean,$(MAKECMDGOALS)),)
-include .dafnydeps.d
endif

# allow non-linear reasoning for nonlin directory specifically
src/Dafny/nonlin/%.dfy.ok: DAFNY_ARGS += /z3opt:smt.arith.nl=true /arith:1

%.dfy.ok: %.dfy
	@echo "DAFNY $<"
	$(Q)$(DAFNY) /compile:0 "$<" 1>/dev/null
	$(Q)touch "$@"

# compilation runs goimports to clean up unused imports emitted by Dafny
bank-go/src/bank.go: src/Dafny/compile.dfy $(DFY_FILES)
	@echo "DAFNY COMPILE $<"
	$(Q)$(DAFNY) /countVerificationErrors:0 /spillTargetCode:2 /out bank $< 1>/dev/null
	$(Q)cd bank-go; \
	env GOPATH="$$PWD" goimports -w ./src
	$(Q)cd bank-go; \
	if [ ! -d src/github.com/mit-pdos/dafny-jrnl ]; then \
		mkdir -p src/github.com/mit-pdos; \
		ln -s ../../../.. src/github.com/mit-pdos/dafny-jrnl; \
	fi

clean:
	@echo "CLEAN"
	$(Q)find . -name "*.dfy.ok" -delete
	$(Q)rm -f .dafnydeps.d
	$(Q)rm -rf bank-go/src/bank.go bank-go/src/*/ bank-go/pkg
