TYPST	= typst
MAIN	= Elements
SRCS	= $(MAIN).typ functions.typ $(wildcard Book*/*.typ) $(wildcard Book*/*.svg) $(wildcard *.jpg) \
	  $(wildcard lean/Elements/Book*/*.lean) lean/lean4.sublime-syntax \
	  $(wildcard lean/SystemE/Theory/*/Space.lean)
PDFS	= ElementsGreekEnglish.pdf ElementsEnglish.pdf LeanElementsOfEuclid.pdf

all:	$(PDFS)

ElementsGreekEnglish.pdf: $(SRCS)
	$(TYPST) compile --input greek=yes $(MAIN).typ $@

ElementsEnglish.pdf: $(SRCS)
	$(TYPST) compile --input greek=no $(MAIN).typ $@

LeanElementsOfEuclid.pdf: $(SRCS)
	$(TYPST) compile --input greek=no --input lean=yes $(MAIN).typ $@

# Check the Lean proofs; needs z3, cvc5 and smt-portfolio.
# `make check BOOK=2` checks one book (and what it imports).
check:
	@if [ -n "$(BOOK)" ] && [ ! -f lean/Elements/Book$(BOOK).lean ]; then \
		echo "No Lean proofs for Book $(BOOK): lean/Elements/Book$(BOOK).lean is missing"; exit 1; fi
	cd lean && lake build $(if $(BOOK),Elements.Book$(BOOK))

# Fetch prebuilt Mathlib; needed once, and after changing the Mathlib version
cache:
	cd lean && lake exe cache get

clean:
	rm -f $(PDFS) $(MAIN).pdf

.PHONY: all clean check cache
