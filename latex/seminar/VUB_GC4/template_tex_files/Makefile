outputname=main.pdf

.PHONY: clean $(outputname) all

all: $(outputname)
$(outputname): $(texfile)
	latexmk -pdf -pdflatex="pdflatex -interaction=nonstopmode" -use-make main.tex

clean:
	latexmk -c -C
	rm _minted-main -rf
