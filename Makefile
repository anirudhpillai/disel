default: Makefile.coq
	$(MAKE) -f Makefile.coq

clean:
	if [ -f Makefile.coq ]; then \
	  $(MAKE) -f Makefile.coq distclean; fi
	rm -f Makefile.coq

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq -no-install \
          -extra-phony 'distclean' 'clean' \
	    'rm -f $$(join $$(dir $$(VFILES)),$$(addprefix .,$$(notdir $$(patsubst %.v,%.aux,$$(VFILES)))))' \
          -extra-phony 'install-core' '' \
	   'cd "Core" && for i in $$(NATIVEFILES1) $$(GLOBFILES1) $$(VFILES1) $$(VOFILES1); do \
         install -d "`dirname "$$(DSTROOT)"$${COQLIB}user-contrib/DiSeL/Core/$$$$i`"; \
         install -m 0644 $$$$i "$$(DSTROOT)"$${COQLIB}user-contrib/DiSeL/Core/$$$$i; \
        done' \
          -extra-phony 'install-heaps' '' \
	   'cd "Heaps" && for i in $$(NATIVEFILES2) $$(GLOBFILES2) $$(VFILES2) $$(VOFILES2); do \
         install -d "`dirname "$$(DSTROOT)"$${COQLIB}user-contrib/DiSeL/Heaps/$$$$i`"; \
         install -m 0644 $$$$i "$$(DSTROOT)"$${COQLIB}user-contrib/DiSeL/Heaps/$$$$i; \
        done' \
          -extra-phony 'install' 'install-heaps install-core' ''

distclean: clean
	rm -f _CoqProject

.PHONY: default clean install distclean
