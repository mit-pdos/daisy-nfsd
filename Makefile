DFY_FILES := $(wildcard src/Dafny/*.dfy)
OK_FILES := $(DFY_FILES:.dfy=.dfy.ok)

Q:=@

all: $(OK_FILES)

.dafnydeps.d: $(DFY_FILES) etc/dafnydep
	@echo "DAFNYDEP"
	$(Q)./etc/dafnydep $(DFY_FILES) > $@

# do not try to build dependencies if cleaning
ifeq ($(filter clean,$(MAKECMDGOALS)),)
-include .dafnydeps.d
endif

%.dfy.ok: %.dfy
	@echo "DAFNY $<"
	$(Q)dafny /compile:0 /nologo /compileVerbose:0 "$<" 1>/dev/null
	$(Q)touch "$@"

clean:
	@echo "CLEAN"
	$(Q)find . -name "*.dfy.ok" -delete
	$(Q)rm -f .dafnydeps.d
