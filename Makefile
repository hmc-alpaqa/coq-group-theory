build: Makefile.coq
	$(MAKE) -f Makefile.coq

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

clean:
	rm -f Makefile.coq *.vo* *.glob *.conf \.*.d \.*.aux