ifeq "$(COQBIN)" ""
  COQBIN=$(dir $(shell which rocq))/
endif

%: Makefile.rocq

Makefile.rocq: _CoqProject
	$(COQBIN)rocq makefile -f _CoqProject -o Makefile.rocq

tests: all
	@$(MAKE) -C tests -s clean
	@$(MAKE) -C tests -s all

-include Makefile.rocq
