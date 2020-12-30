DFY_FILES := $(wildcard src/Dafny/*.dfy)
OK_FILES := $(DFY_FILES:.dfy=.dfy.ok)

all: $(OK_FILES)

%.dfy.ok: %.dfy
	@echo "DAFNY $<"
	@dafny /compile:0 /nologo /compileVerbose:0 "$<" 1>/dev/null
	@touch "$@"

clean:
	find . -name "*.dfy.ok" -delete
