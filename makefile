test:
	ocamlbuild -use-ocamlfind -pkgs ounit2 tests.native && ./tests.native
