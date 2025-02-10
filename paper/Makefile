SRC := paper.tex \
       intro.tex \
       background.tex \
       performance.tex \
       conclusions.tex \
       paper.bib

all: paper.pdf


.PHONY: paper.tex
paper.tex : latex/arrays.tex latex/lang.tex latex/ad.tex latex/performance.tex

latex/%.tex : %.lagda
	agda --latex $< #--only-scope-checking $<

paper.pdf: $(SRC)
	TEXINPUTS=./latex:$$TEXINPUTS latexmk -pdf -f -pdflatex='pdflatex -halt-on-error' $<

paper.zip: $(SRC) latex/arrays.tex # paper.bbl acmart.cls
	$(RM) paper.zip
	zip paper.zip $(SRC) latex/model.tex paper.bbl acmart.cls

clean:
	latexmk -c
	$(RM) *.ptb *.bbl 
