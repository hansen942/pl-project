MAIN := main.cmo
OBJS := definitions.cmo evallambda.cmo typecheck.cmo main.cmo tests.cmo

%.cmo: %.ml
	ocamlc -c $<

%.cmi: %.mli
	ocamlc -c $<

$(MAIN): $(OBJS)
	ocamlc -o $@ $^

lexer.ml: lexer.mll
	ocamllex -q $<

parser.ml: parser.mly
	ocamlyacc -q $<

parser.mli: parser.mly
	ocamlyacc -q $<

clean:
	rm -f *.cmo *.cmi

# Dependencies generated by `ocamldep -bytecode *.mli *.ml`.
eval_lambda.cmo : definitions.cmo

test : 
	ocaml tests.ml
