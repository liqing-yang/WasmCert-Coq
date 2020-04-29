.PHONY: all clean

all:
	export HOME=`pwd`; dune build @all || chmod +w _build/default/theories/.*.aux ; dune build @all # Dirty fix to WTF Dune bug, that I failed to reproduce outside this context.
	dune build -p wasm_interpreter

clean:
	rm -rf _build || true
	rm theories/*.vo || true
	rm theories/*.glob || true
	rm theories/*.aux || true
	rm src/extract.{ml,mli} || true

