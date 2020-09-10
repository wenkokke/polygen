default: doc/main.pdf

doc/main.pdf: doc/main.tex
	cd doc && latexmk -pdf main.tex

doc/main.tex: doc/main.lhs src/polygen.lhs
	lhs2TeX doc/main.lhs -o doc/main.tex
