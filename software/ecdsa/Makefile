all: dist/libk2.a

# Boilerplate
# -----------

include Makefile.include

FST_FILES=$(wildcard src/*.fst) $(wildcard src/*.fsti)

ifndef NODEPEND
ifndef MAKE_RESTARTS
.depend: .FORCE
	mkdir -p obj
	$(FSTAR) --dep full $(FST_FILES) > $@

.PHONY: .FORCE
.FORCE:
endif
endif

include .depend

.PHONY: clean
clean:
	rm -rf obj dist .depend *.exe

# Verification
# ------------

hints obj:
	mkdir $@

%.checked: | hints obj
	$(FSTAR) --hint_file hints/$(notdir $*).hints $(notdir $*) && touch -c $@

%.krml:
	$(FSTAR) --codegen krml \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<))

# Karamel
# -------

KRML=$(KRML_HOME)/krml

# The usual bug with prims.krml
dist/Makefile.basic: $(filter-out %prims.krml,$(ALL_KRML_FILES))
	$(KRML) $(KOPTS) -library EverCrypt,EverCrypt.* $^ -tmpdir dist -skip-compilation \
	  -minimal \
	  -add-include '"krml/internal/target.h"' \
	  -add-include '"krml/internal/types.h"' \
	  -add-include '"krml/lowstar_endianness.h"' \
	  -add-include '<stdint.h>' \
	  -add-include '<stdbool.h>' \
	  -add-include '<string.h>' \
	  -fparentheses \
	  -o libk2.a \
	  -no-prefix 'K2' \
	  -bundle 'K2+K2.Ecdsa.Impl=K2.*[rename=K2]' \
	  -bundle LowStar.* \
	  -bundle Prims,C.Failure,C,C.String,C.Loops,Spec.Loops,C.Endianness,FStar.*[rename=K2_Krmllib] \
	  -bundle 'Meta.*,Hacl.*,Spec.*,Lib.*,EverCrypt,EverCrypt.*[rename=K2_EverCrypt]'

dist/libk2.a: dist/Makefile.basic
	$(MAKE) -C dist -f Makefile.basic

# Tests
# -----

.PHONY: test
test: test.exe
	./$<

CFLAGS+=-Idist -Itests -I$(KRML_HOME)/include -I$(KRML_HOME)/krmllib/dist/minimal

$(HACL_HOME)/dist/gcc-compatible/libevercrypt.a:
	$(error Please run make in $(dir $@))
