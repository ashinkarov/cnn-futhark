SRC_TEX=paper.tex intro.tex performance.tex relatedwork.tex conclusions.tex
SRC=$(SRC_TEX) paper.bib

all: paper.pdf


.PHONY: paper.tex
paper.tex : latex/arrays.tex latex/lang.tex latex/ad.tex ad-example.pdf

ad-example.pdf: ad-example.tex
	TEXINPUTS=./latex:$$TEXINPUTS latexmk -pdf -f -pdflatex='pdflatex -halt-on-error' $<

latex/%.tex : %.lagda
	agda --latex -l standard-library -i . $< #--only-scope-checking $<

paper.pdf: $(SRC)
	TEXINPUTS=./latex:$$TEXINPUTS latexmk -pdf -f -pdflatex='pdflatex -halt-on-error' $<

paper.zip: $(SRC) latex/arrays.tex latex/lang.tex latex/ad.tex latex/agda.sty ad-example.pdf paper.bbl acmart.cls mathpartir.sty ACM-Reference-Format.bst
	$(RM) paper.zip
	zip paper.zip $(SRC) latex/arrays.tex latex/lang.tex latex/ad.tex latex/agda.sty ad-example.pdf paper.bbl acmart.cls mathpartir.sty ACM-Reference-Format.bst

diff/%.tex: %.tex
	latexdiff --config PICTUREENV='code|wrapfigure' --graphics-markup=none submitted/$*.tex $*.tex > $@

paper-diff.pdf: $(SRC_TEX:%=diff/%) diff/latex/arrays.tex diff/latex/lang.tex diff/latex/ad.tex
	TEXINPUTS=./diff/latex:$$TEXINPUTS latexmk -output-directory=diff -pdf -f -pdflatex='pdflatex -halt-on-error' paper.tex
	mv diff/paper.pdf $@

clean:
	latexmk -c
	$(RM) *.ptb *.bbl 
