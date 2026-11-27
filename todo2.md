# Milestone 2 — Book 2: tasks

Book 2 has 14 propositions, all in System E, building on Book 1's area results (Props. 1.34–1.47). The tasks run in order. Each one ends with `make check BOOK=2` and `make` passing, then a commit. The common rules in [Roadmap.md](Roadmap.md) apply throughout.

A proof's file `lean/Elements/Book2/PropNN.lean` and the `#lean-proof("/lean/Elements/Book2/PropNN.lean")` line in `Book02/PropNN.typ` are always added in the same task. Typst's `read` fails on a missing file.

## T7. Props. 2.7–2.8

2.7: the squares on the whole and on one piece equal twice the rectangle plus the square on the other piece. 2.8: four times the rectangle plus a square, set out on a line produced. Prop. 2.8 is long, with eight parallelograms. Split it into `have` steps so each SMT query stays small.

## T8. Props. 2.9–2.10: sums of squares

These are proved by isosceles right triangles and Prop. 1.47, not gnomons. They use Props. 1.5, 1.6, 1.29, 1.32 and 1.34. Prop. 2.10 is the produced-line form of 2.9, as 2.6 is of 2.5.

## T9. Prop. 2.11: cutting a line in extreme and mean ratio

This is a construction problem: there exists a point H on AB with rect(AB, BH) = sq(AH). It uses Props. 1.10, 1.3, 1.46, 1.47 and 2.6. Prop. 4.10 and Book 13 need this statement later, so state it in the form they will need.

## T10. Props. 2.12–2.13: the law of cosines

2.12 is the obtuse triangle, with the perpendicular falling outside. 2.13 is the acute angle. Both use Props. 1.12, 1.47, 2.4 and 2.7.
- Euclid proves 2.13 for one position of the foot of the perpendicular only. Prove the case he proves.
- If the formal statement needs the position as a hypothesis, mark that `-- Missed by Euclid.` and note it in the primer's list of gaps.
- Watch the angle conditions "obtuse" and "acute", written as `> ∟` and `< ∟`.

## T11. Prop. 2.14: squaring a rectilinear figure

This is the end of Book 2. It uses Prop. 1.45 for the parallelogram, then a semicircle, Prop. 2.5 and Prop. 1.47.
- **The given figure.** State the "given rectilinear figure" as Prop. 1.45 does: a quadrilateral made of two triangles.
- **The semicircle.** The point where the perpendicular meets the circle comes from the line–circle intersection rules. Euclid takes it from the figure, so expect `-- Missed by Euclid.` steps.
- **The degenerate case.** Euclid handles separately the case where the parallelogram is already a square. Include it as he does.

## T12. Primer and docs

- `Book00/Lean.typ`: reword "the propositions of Book 1" for several books, and explain the convention for rectangles and squares from `lean/Elements/Book2.lean`.
- Typeset `lean/Elements/Book2/Lemmas.lean` (`rectangle_on`, `rectangle_on'` and later lemmas) in the Lean edition, e.g. after Book 2's definitions, so readers see what the proofs call.
- `CLAUDE.md`: the Lean project notes for Book 2, and where `lean/Elements/Book2/Lemmas.lean` fits.
- `Roadmap.md`: mark Milestone 2 done in the table.

## T13. Final check

- Run `make check` from clean, all books, and note the time.
- `grep -r sorry lean/` finds nothing.
- Inspect `ElementsLean.pdf` pages: the title subtitle, Book 2's title page, the long proofs (2.8, 2.14), and the corollary to 2.4.
- Confirm `ElementsEnglish.pdf` and `ElementsGreekEnglish.pdf` are unchanged.
- Commit, push, and update the README if the release PDFs are rebuilt.
