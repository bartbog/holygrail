# LaTeX Makefile -- LaTeX only

# set the path to your TeX file here
FILENAME=masterproef

PAPER=$(FILENAME).tex
SHELL=/bin/zsh          # for the while loop below

.PHONY: masterproef.pdf all clean watch

all: main
open: main
	xdg-open $(FILENAME).pdf &


%.tex: %.raw
	./raw2tex $< > $@
%.tex: %.dat
	./dat2tex $< > $@

# MAIN LATEXMK RULE
# -
# -pdf tells latexmk to generate PDF directly (instead of DVI).
# -pdflatex="" tells latexmk to call a specific backend with specific options.
# -use-make tells latexmk to call make for generating missing files.

# -interaction=nonstopmode keeps the pdflatex backend from stopping at a
# missing file reference and interactively asking you for an alternative.
main: $(FILENAME).tex
	latexmk -pdf $(PREVIEW_CONTINUOUSLY) -bibtex -pdflatex="pdflatex -interaction=nonstopmode" -use-make $(FILENAME).tex
watch: PREVIEW_CONTINUOUSLY=-pvc
watch: main

clean:
	latexmk -CA


mainTom:  ## Compile paper
	rubber --pdf $(PAPER)


cleanTom:  ## Clean output files
	rubber --clean $(PAPER)

watchTom: main
watchTom: main ## Recompile on updates to the source file
	@while [ 1 ]; do; inotifywait *.tex; sleep 0.01; make all; done
