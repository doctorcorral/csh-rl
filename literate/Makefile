# Makefile for literate Agda CSHRL documents
# Requires: agda, lualatex

MAIN = CSHRL
APPENDIX = CSHRL-Appendix
SYNTHESIS = CSHRLSynthesis
ICFP = CSHRL-ICFP
AGDA = agda
LATEX = lualatex
LATEX_FLAGS = -interaction=nonstopmode

.PHONY: all clean agda pdf appendix synthesis agda-synthesis icfp agda-icfp demos

all: pdf appendix synthesis

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

# Synthesis document (main + demos appendix)
agda-synthesis: $(SYNTHESIS).lagda.tex $(SYNTHESIS)-Demos.lagda.tex
	$(AGDA) --latex $(SYNTHESIS).lagda.tex
	$(AGDA) --latex $(SYNTHESIS)-Demos.lagda.tex
	cp agda-spec.sty latex/

synthesis: agda-synthesis
	cd latex && $(LATEX) $(LATEX_FLAGS) $(SYNTHESIS).tex
	cd latex && $(LATEX) $(LATEX_FLAGS) $(SYNTHESIS).tex
	cp latex/$(SYNTHESIS).pdf .

# Demos appendix (included in synthesis; this target is an alias)
demos: synthesis

# ICFP submission (ACM Small format)
agda-icfp: $(ICFP).lagda.tex
	$(AGDA) --latex $<
	cp agda-spec.sty latex/
	cp cshrl-icfp.bib latex/

icfp: agda-icfp
	cd latex && $(LATEX) $(LATEX_FLAGS) $(ICFP).tex
	cd latex && bibtex $(ICFP)
	cd latex && $(LATEX) $(LATEX_FLAGS) $(ICFP).tex
	cd latex && $(LATEX) $(LATEX_FLAGS) $(ICFP).tex
	cp latex/$(ICFP).pdf .

# Clean build artifacts
clean:
	rm -rf latex/
	rm -f $(MAIN).pdf $(APPENDIX).pdf $(SYNTHESIS).pdf
	rm -f *.agdai
	rm -rf _build/

# Watch for changes (requires fswatch)
watch:
	fswatch -o *.lagda.tex | xargs -n1 -I{} make all

