all: \
	string.json K2.json K2_EverCrypt.json i64_shl.json i64_shr.json dummy.json Lib_Memzero0.json

i64_%.json: ../impl/fw/i64_%.c $(shell find ../impl/fw -name '*.h')
	ccomp -I../impl/fw -I../impl/fw/hacl -fno-fpu -std=c18 -fstruct-passing -fpacked-structs -sdump $< -S
	@python3 -m json.tool $@ > $@_tmp
	@mv $@_tmp $@
	sed -i -e 's/"i64_/"__compcert_i64_/g' $@

%.json: ../impl/fw/%.c $(shell find ../impl/fw -name '*.h')
	ccomp -I../impl/fw -I../impl/fw/hacl -fno-fpu -std=c18 -fstruct-passing -fpacked-structs -sdump $< -S
	@python3 -m json.tool $@ > $@_tmp
	@mv $@_tmp $@

%.json: ../impl/fw/hacl/%.c $(shell find ../impl/fw -name '*.h')
	ccomp -I../impl/fw -I../impl/fw/hacl -fno-fpu -std=c18 -fstruct-passing -fpacked-structs -sdump $< -S
	@python3 -m json.tool $@ > $@_tmp
	@mv $@_tmp $@


.PHONY: clean
clean:
	rm -f *.json *.s *_tmp
