
Makefile.coq: _CoqProject
	@$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

include Makefile.coq

clean::
	rm -f Makefile.coq
	rm -f Makefile.coq.conf

.PHONY: clean
