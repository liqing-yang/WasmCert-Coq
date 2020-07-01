.PHONY: all clean

# FIXME: export HOME=`pwd`; dune build @all --verbose || chmod +w _build/default/theories/.*.aux ; dune build @all # Dirty fix to WTF Dune bug, that I failed to reproduce outside this context.
all: .vscode/settings.json
	export HOME=`pwd`; dune build @all --verbose
	dune build -p wasm_interpreter
	ln -f -s ./_build/install/default/bin/wasm_interpreter ./wasm_interpreter

clean:
	rm -rf _build || true
	rm theories/*.vo || true
	rm theories/*.glob || true
	rm theories/*.aux || true
	rm src/extract.{ml,mli} || true
	rm theories/extract.{ml,mli} || true

.vscode/settings.json:
	mkdir -p .vscode
	echo $(VSCODESETTINGS) > $@

