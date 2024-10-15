
all:
	@cd src; \
	ocamlyacc -v maude_parser.mly; \
	ocamllex maude_lexer.mll; \
	ocamlyacc -v input_parser.mly; \
	ocamllex input_lexer.mll; \
	ocamlopt -o ../fvpgen -I +unix unix.cmxa statistic.mli statistic.ml utils.mli utils.ml term.ml input_function.ml input_parser.mli input_parser.ml\
		input_lexer.ml maude_function.ml maude_parser.mli maude_parser.ml maude_lexer.ml pvqueue.mli pvqueue.ml flattened.ml rule_queue.mli\
		rule_queue.ml AC.mli AC.ml order.mli order.ml rewrite_rule.ml main.ml

dune:
	@cd src; \
	dune build; \
	cd ..; \
	cp src/main.exe fvpgen

clean:
	@cd src; rm -f *.cmi *.cmx *.output input_parser.mli input_parser.ml input_lexer.ml maude_lexer.ml maude_parser.mli maude_parser.ml *o
	@cd src; dune clean
	@rm -f fvpgen src/main.exe