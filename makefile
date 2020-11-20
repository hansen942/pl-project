test:
	ocamlbuild -use-ocamlfind -pkgs ounit2 tests.native && ./tests.native
play:
	ocamlbuild playground.native && ./playground.native

