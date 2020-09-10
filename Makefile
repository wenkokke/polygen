default: doc/main.pdf

.PHONY: build
build: src/polygen.hs
	stack build

.PHONY: paper
paper: doc/main.pdf

doc/main.pdf: doc/main.tex
	cd doc && latexmk -pdf main.tex

doc/main.tex: doc/*.lhs
	cd doc && lhs2TeX main.lhs -o main.tex

src/:
	mkdir src/

src/polygen.hs: src/ | doc/polygen.lhs
	cd doc && lhs2TeX --newcode main.lhs -o ../src/polygen.hs
