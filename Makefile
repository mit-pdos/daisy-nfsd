DFY_FILES := $(shell find src -name "*.dfy")
OK_FILES := $(DFY_FILES:.dfy=.dfy.ok)

# these arguments don't affect verification outcomes
DAFNY_BASIC_ARGS := /compile:0 /compileTarget:go /timeLimit:20 /vcsLoad:0.5
DAFNY_ARGS := /noNLarith /arith:5
DAFNY=./etc/dafnyq $(DAFNY_BASIC_ARGS) $(DAFNY_ARGS)

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
src/Dafny/nonlin/%.dfy.ok: DAFNY_ARGS = /arith:1

%.dfy.ok: %.dfy
	@echo "DAFNY $<"
	$(Q)$(DAFNY) "$<"
	$(Q)touch "$@"

# compilation runs goimports to clean up unused imports emitted by Dafny
# the call to gofmt simplifies the code to make it more readable
bank-go/src/bank.go: src/Dafny/compile.dfy $(DFY_FILES)
	@echo "DAFNY COMPILE $<"
	$(Q)$(DAFNY) /countVerificationErrors:0 /spillTargetCode:2 /out bank $<
	$(Q)cd bank-go; \
	env GOPATH="$$PWD" goimports -w ./src; \
	env GOPATH="$$PWD" gofmt -r '(a) -> a' -w ./src
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
