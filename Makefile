default: paper

.PHONY: init
init:
	stack install lhs2tex

.PHONY: paper
paper: doc/paper.pdf

doc/paper.pdf: doc/paper.tex
	cd doc && latexmk -pdflua paper.tex

doc/paper.tex: doc/main.tex doc/PolyGen.lhs
	cd doc && stack exec -- lhs2TeX main.tex -o paper.tex

.PHONY: clean
clean:
	cd doc && latexmk -f -C paper
	rm doc/paper.tex
