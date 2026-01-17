# Makefile for literate Agda CSHRL documents
# Requires: agda, lualatex

MAIN = CSHRL
APPENDIX = CSHRL-Appendix
AGDA = agda
LATEX = lualatex
LATEX_FLAGS = -interaction=nonstopmode

.PHONY: all clean agda pdf appendix

all: pdf appendix

# Main document
agda: $(MAIN).lagda.tex
	$(AGDA) --latex $<
	cp agda-spec.sty latex/  # Copy spec environment support

pdf: agda
	cd latex && $(LATEX) $(LATEX_FLAGS) $(MAIN).tex
	cd latex && $(LATEX) $(LATEX_FLAGS) $(MAIN).tex
	cp latex/$(MAIN).pdf .

# Appendix document
agda-appendix: $(APPENDIX).lagda.tex
	$(AGDA) --latex $<

appendix: agda-appendix
	cd latex && $(LATEX) $(LATEX_FLAGS) $(APPENDIX).tex
	cd latex && $(LATEX) $(LATEX_FLAGS) $(APPENDIX).tex
	cp latex/$(APPENDIX).pdf .

# Clean build artifacts
clean:
	rm -rf latex/
	rm -f $(MAIN).pdf $(APPENDIX).pdf
	rm -f *.agdai
	rm -rf _build/

# Watch for changes (requires fswatch)
watch:
	fswatch -o *.lagda.tex | xargs -n1 -I{} make all

