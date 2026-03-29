XELATEX = xelatex -interaction=nonstopmode
BIBER   = biber

.PHONY: all light dark clean

all: light dark

light: main.pdf
dark:  main-dark.pdf

main.pdf: main.tex preamble.tex preface.tex sections/*.tex appendices/*.tex bibliography.bib
	$(XELATEX) main.tex
	$(BIBER)   main
	$(XELATEX) main.tex
	$(XELATEX) main.tex

main-dark.pdf: main-dark.tex preamble.tex darkmode.sty preface.tex sections/*.tex appendices/*.tex bibliography.bib
	$(XELATEX) main-dark.tex
	$(BIBER)   main-dark
	$(XELATEX) main-dark.tex
	$(XELATEX) main-dark.tex

clean:
	rm -f *.aux *.log *.out *.toc *.lof *.lot *.bbl *.bcf *.blg *.run.xml
	rm -f *.fls *.fdb_latexmk *.synctex.gz
	rm -f sections/*.aux appendices/*.aux preface.aux
