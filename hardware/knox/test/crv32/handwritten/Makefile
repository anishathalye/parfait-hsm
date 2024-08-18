all: \
	return.json \
	init_value.json \
	stack.json \
	goto.json \
	pointer_comparison.json \
	addl.json \
	builtins.json \
	implicit_memcpy.json \
	popcnt_verif.json \
	memory_io.json \
	link1.json \
	link2.json \
	solve.json \
	table.json \
	divrem.json \
	function_pointer.json \
	shift_and_compare.json \
	misc.json \
	sha256.json \
	sha256_main.json \
	branch_stack_merge.json \
	use_after_free.json \
	stack_reference.json \


%.json: %.c $(shell find . -name '*.h')
	ccomp -fno-fpu -std=c18 -fstruct-passing -sdump $< -S
	@sed -i -e 's/:".*\/knox\/test\/crv32\/handwritten"/:"\/knox\/test\/crv32\/handwritten"/' -e 's/command" :".*ccomp /command" :"ccomp /' $@
	@python -m json.tool $@ > $@_tmp
	@mv $@_tmp $@

.PHONY: clean
clean:
	rm -f *.json *.s *_tmp
