.PHONY: watch

all: *.tex
	pdflatex -shell-escape main
	bibtex main
	pdflatex -shell-escape main
	pdflatex -shell-escape main

watch:
	make all; \
	while true; do \
		inotifywait --event modify *.tex; \
		make all; \
	done

clean:
	rm *.aux *.log *.cut *.bbl *.pdf *.blg *.out
