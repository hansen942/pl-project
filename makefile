test:
	ocamlbuild -use-ocamlfind -pkgs ounit2 tests.native && ./tests.native

build:
	ocamlbuild -use-ocamlfind -lib unix main.native

clean:
	rm -f main.native
	rm -f tests.native

doc: build
	ocamldoc -html -d _ocamldoc definitions.ml typecheck.ml evallambda.ml main.ml -I _build
