.PHONY: all
all: hsm.rkt

SOC_V := $(shell find ../impl/hw -name '*.v' -o -name '*.sv')

MEM := ../impl/fw/firmware.mem

.PHONY: FORCE

$(MEM): FORCE
	$(MAKE) -C ../impl/ fw/firmware.mem

../impl/combined.v: $(SOC_V)
	sv2v -D SYNTHESIS -D YOSYS $^ > $@

hsm.smt2: ../impl/combined.v $(MEM)
	cd ../impl; \
	yosys \
		-p "read_verilog -defer $<" \
		-p 'prep -flatten -top hsm -nordff' \
		-p 'write_smt2 -stdt ../proof/hsm.smt2'

hsm.rkt: hsm.smt2
	echo '#lang yosys' > $@
	cat $< >> $@

.PHONY: clean
clean:
	$(MAKE) -C ../impl/ clean
	rm -f hsm.rkt hsm.smt2
