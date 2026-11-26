TYPST	= typst
MAIN	= Elements
SRCS	= $(MAIN).typ functions.typ $(wildcard Book*/*.typ) $(wildcard Book*/*.svg) $(wildcard *.jpg)
PDFS	= ElementsGreekEnglish.pdf ElementsEnglish.pdf

all:	$(PDFS)

ElementsGreekEnglish.pdf: $(SRCS)
	$(TYPST) compile --input greek=yes $(MAIN).typ $@

ElementsEnglish.pdf: $(SRCS)
	$(TYPST) compile --input greek=no $(MAIN).typ $@

clean:
	rm -f $(PDFS) $(MAIN).pdf

.PHONY: all clean
