all: Makefile.coq
	$(MAKE) -f Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

Makefile.coq:
	rocq makefile -f _CoqProject -o Makefile.coq

autosubst:
	cd theories/autosubst ; \
	$(MAKE) -f Makefile

force _CoqProject Makefile: ;

doc: coqdoc
	pandoc --standalone --output=doc/index.html --css=doc/github-pandoc.css --metadata title="Local Comp Overview" doc/index.md

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

.PHONY: all clean autosubst
