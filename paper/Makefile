SRC := paper.tex \
       intro.tex \
       performance.tex \
       relatedwork.tex \
       conclusions.tex \
       paper.bib

all: paper.pdf


.PHONY: paper.tex
paper.tex : latex/arrays.tex latex/lang.tex latex/ad.tex

latex/%.tex : %.lagda
	agda --latex -l standard-library -i . $< #--only-scope-checking $<

paper.pdf: $(SRC)
	TEXINPUTS=./latex:$$TEXINPUTS latexmk -pdf -f -pdflatex='pdflatex -halt-on-error' $<

paper.zip: $(SRC) latex/arrays.tex # paper.bbl acmart.cls
	$(RM) paper.zip
	zip paper.zip $(SRC) latex/model.tex paper.bbl acmart.cls

clean:
	latexmk -c
	$(RM) *.ptb *.bbl 
