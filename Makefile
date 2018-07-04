Spec := Uptane

WORKERS := $(shell nproc || echo 4)

TLA := docker run -u $(shell id -u):$(shell id -g) --rm -it --workdir /mnt -v ${PWD}:/mnt talex5/tla

.PHONY: all check tlaps pdfs

all: check pdfs # tlaps

check:
	${TLA} tlc -workers ${WORKERS} ${Spec}.tla

tlaps:
	${TLA} tlapm -I /usr/local/lib/tlaps ${Spec}.tla

%.pdf: %.tla
	[ -d metadir ] || mkdir metadir
	${TLA} java tla2tex.TLA -shade -latexCommand pdflatex -latexOutputExt pdf -metadir metadir $<

pdfs: ${Spec}.pdf
