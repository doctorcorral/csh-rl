all: Makefile.coq
	$(MAKE) -f Makefile.coq

# Rocq >= 9 renamed coq_makefile to `rocq makefile`; support both.
Makefile.coq: _CoqProject
	if command -v coq_makefile >/dev/null 2>&1; then \
	  coq_makefile -f _CoqProject -o Makefile.coq; \
	else \
	  rocq makefile -f _CoqProject -o Makefile.coq; \
	fi

clean:
	if [ -f Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	rm -f Makefile.coq Makefile.coq.conf

.PHONY: all clean
