# MICAI 2026 submission build.
# Renders the literate Agda source with native syntax highlighting:
#   agda --latex  ->  lualatex (llncs class).
# Requires: agda (2.8.x) with standard-library, lualatex.

AGDA     = agda
LATEX    = lualatex
LFLAGS   = -interaction=nonstopmode
MAIN     = paper
TEMPLATE = LaTeX2e+Proceedings+Templates+download

.PHONY: micai all clean

# Convenience alias: `make micai`
micai: all

all:
	$(AGDA) --latex $(MAIN).lagda.tex
	cp "$(TEMPLATE)/llncs.cls" latex/
	cp "$(TEMPLATE)/splncs04.bst" latex/
	cp agda-spec.sty latex/
	cd latex && $(LATEX) $(LFLAGS) $(MAIN).tex
	cd latex && $(LATEX) $(LFLAGS) $(MAIN).tex
	cp latex/$(MAIN).pdf .
	@echo "Built $(MAIN).pdf"

clean:
	rm -rf latex _build *.agdai _agda_build.log
