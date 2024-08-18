.PHONY: all
all: hsm.rkt

SOC_V := $(shell find ../impl/hw/soc -name '*.v')

MEM := ../impl/fw/firmware.mem

.PHONY: FORCE

$(MEM): FORCE
	$(MAKE) -C ../impl/ fw/firmware.mem

hsm.smt2: ../impl/hw/hsm.v $(SOC_V) $(MEM)
	cd ../impl; \
	yosys \
		-p "read_verilog -defer $< $$(find hw/soc -name '*.v' | tr '\n' ' ')" \
		-p 'prep -flatten -top hsm -nordff' \
		-p 'write_smt2 -stdt ../proof/hsm.smt2'

hsm.rkt: hsm.smt2
	echo '#lang yosys' > $@
	cat $< >> $@

.PHONY: clean
clean:
	rm -f hsm.rkt hsm.smt2
