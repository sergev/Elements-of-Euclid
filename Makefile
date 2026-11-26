TYPST	= typst
MAIN	= Elements
SRCS	= $(MAIN).typ functions.typ $(wildcard Book*/*.typ) $(wildcard Book*/*.svg) $(wildcard *.jpg) \
	  $(wildcard lean/Elements/Book1/*.lean) lean/lean4.sublime-syntax
PDFS	= ElementsGreekEnglish.pdf ElementsEnglish.pdf ElementsLean.pdf

all:	$(PDFS)

ElementsGreekEnglish.pdf: $(SRCS)
	$(TYPST) compile --input greek=yes $(MAIN).typ $@

ElementsEnglish.pdf: $(SRCS)
	$(TYPST) compile --input greek=no $(MAIN).typ $@

ElementsLean.pdf: $(SRCS)
	$(TYPST) compile --input greek=no --input lean=yes $(MAIN).typ $@

# Check the Lean proofs; needs z3, cvc5 and smt-portfolio
check:
	cd lean && lake exe cache get && \
	LD_LIBRARY_PATH="$$(lean --print-prefix)/lib/lean$${LD_LIBRARY_PATH:+:$$LD_LIBRARY_PATH}" lake build

clean:
	rm -f $(PDFS) $(MAIN).pdf

.PHONY: all clean check
