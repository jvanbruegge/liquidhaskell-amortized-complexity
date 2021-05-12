.PHONY: watch

all: *.tex
	pdflatex main
	bibtex main
	pdflatex main
	pdflatex main

watch:
	make all; \
	while true; do \
		inotifywait --event modify main.tex; \
		make all; \
	done
