# Milestone 2 — Book 2: tasks

Book 2 has 14 propositions, all in System E, building on Book 1's area results (Props. 1.34–1.47). The tasks run in order. Each one ends with `make check BOOK=2` and `make` passing, then a commit. The common rules in [Roadmap.md](Roadmap.md) apply throughout.

A proof's file `lean/Elements/Book2/PropNN.lean` and the `#lean-proof("/lean/Elements/Book2/PropNN.lean")` line in `Book02/PropNN.typ` are always added in the same task. Typst's `read` fails on a missing file.

## T13. Final check

- Run `make check` from clean, all books, and note the time.
- `grep -r sorry lean/` finds nothing.
- Inspect `ElementsLean.pdf` pages: the title subtitle, Book 2's title page, the long proofs (2.8, 2.14), and the corollary to 2.4.
- Confirm `ElementsEnglish.pdf` and `ElementsGreekEnglish.pdf` are unchanged.
- Commit, push, and update the README if the release PDFs are rebuilt.
