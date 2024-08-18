.PHONY: all
all: fw/firmware.mem fw/firmware.lst

.PHONY: clean
clean:
	rm -rf $(CLEAN_FILES)

HEADERFILES := $(shell find fw -name '*.h')

include ../../common/impl/Makefrag

ROM_DEPTH := 32768

include fw/Makefrag
