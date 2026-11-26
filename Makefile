TYPST	= typst
MAIN	= ElementsTypst
SRCS	= $(MAIN).typ functions.typ $(wildcard Book*/*.typ)

all:	$(MAIN).pdf

$(MAIN).pdf: $(SRCS)
	$(TYPST) compile $(MAIN).typ $@

clean:
	rm -f $(MAIN).pdf

.PHONY: all clean
