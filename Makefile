default: paper

.PHONY: paper
paper: doc/paper.pdf

doc/paper.pdf: doc/paper.tex
	cd doc && latexmk -pdf paper.tex

doc/paper.tex: doc/main.tex doc/PolyGen.lhs
	cd doc && lhs2TeX main.tex -o paper.tex

.PHONY: clean
clean:
	cd doc && latexmk -f -C paper
	rm doc/paper.tex
