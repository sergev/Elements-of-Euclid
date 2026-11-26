TYPST	= typst
MAIN	= Elements
SRCS	= $(MAIN).typ functions.typ $(wildcard Book*/*.typ) $(wildcard Book*/*.svg) $(wildcard *.svg)

all:	$(MAIN).pdf

$(MAIN).pdf: $(SRCS)
	$(TYPST) compile $(MAIN).typ $@

clean:
	rm -f $(MAIN).pdf

.PHONY: all clean
