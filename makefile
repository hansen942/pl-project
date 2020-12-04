test:
	ocamlbuild -use-ocamlfind -pkgs ounit2 tests.native && ./tests.native
play:
	ocamlbuild playground.native && ./playground.native

build:
	ocamlbuild main.native

clean:
	rm -f main.native
	rm -f tests.native

doc: build
	ocamldoc -html -d _ocamldoc definitions.ml typecheck.ml evallambda.ml main.ml -I _build
