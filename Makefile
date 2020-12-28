DFY_FILES := $(wildcard src/Dafny/*.dfy)
OK_FILES := $(DFY_FILES:.dfy=.dfy.ok)

all: $(OK_FILES)

%.dfy.ok: %.dfy
	dafny /compile:0 "$<"
	touch "$@"
