# Milestone 6 — Book 6: tasks

Book 6 applies Book 5's proportion to figures: 33 propositions about triangles and parallelograms whose sides or areas are proportional, and about similar figures. It has corollaries to 6.8, 6.19 and 6.20.
- 6.1–6.3: equal heights, parallels, the bisector of an angle.
- 6.4–6.8: equiangular and similar triangles.
- 6.9–6.13: constructions: a part, a cut line, third, fourth and mean proportionals.
- 6.14–6.17: reciprocal proportion; rectangles of proportionals.
- 6.18–6.22: similar figures and the squared ratio.
- 6.23–6.26: the compounded ratio, parallelograms about the diagonal.
- 6.27–6.30: application of areas, and extreme and mean ratio.
- 6.31–6.33: the generalized Pythagoras, triangles placed together, angles and arcs.

The tasks run in order. The common rules in [Roadmap.md](Roadmap.md) apply throughout, and so does Milestone 6 there: the decisions on `Length` and `Area`.

## Routine for every task

- Each task ends with these steps:
  - `make check BOOK=6` and `make` pass;
  - `tools/gaps.sh 6` finds no failing steps, and `Lemmas.lean` and `Definitions.lean` check with `systemE.smt` off;
  - `grep -r sorry lean/Elements/Book6` finds nothing;
  - commit, and remove the task from this file.
- A proposition's `lean/Elements/Book6/PropNN.lean` and its `#lean-proof(...)` line in `Book06/PropNN.typ` go in together.
- Inside `namespace Elements.Book6`, write `Elements.BookN.proposition_M` in full for other books' propositions.
- Keep Lean lines to 90 characters, so that they don't wrap in the PDF.
- Run every check under `systemd-run --user --scope -q -p MemoryMax=6G -p MemorySwapMax=0`. Never use `maxHeartbeats 0`; a finite limit is fine.

How Book 6 differs from Books 1–5:
- **Two kinds of step.** Geometric steps are System E's, closed by saturation (`euclid_apply`, `euclid_assert`, `euclid_finish`), SMT-free as in Books 1–4. Steps about ratios are Book 5's propositions, applied as plain Lean terms; saturation knows nothing of `Proportion`. Keep the two apart: get the equal lengths, areas and angles from the figure, turn them into `Length`/`Area` equalities, then cite Book 5.
- **Faithfulness to Book 5.** Every ratio step cites a Book 5 proposition or Def. 5.5. Don't use `Positive.proportion_of_mul_eq`, `Positive.mult_val` or `Length.fourth` where Euclid has an argument; they are facts of the model. Record each use, with the reason, in a comment.
- **No reals for ratios.** A ratio of lines or areas is never `|(a─b)| / |(c─d)|`.

## T8. Props. 6.23–6.26: the compounded ratio, parallelograms about the diagonal

- **6.23:** equiangular parallelograms are in the ratio compounded of their sides. Uses T1's definition.
- **6.24:** parallelograms about the diagonal are similar to the whole and to one another.
- **6.25:** a figure similar to one figure and equal to another. Uses 1.44, 1.45 and 6.13; the given figures are as far as 1.45 reaches (T1).
- **6.26:** the converse of 6.24, by contradiction.

## T9. Props. 6.27–6.30: application of areas

- **6.27:** of parallelograms applied to a line and falling short by figures similar to the one on half the line, the one on half is the greatest.
- **6.28:** to apply a parallelogram falling short; with its condition (the given figure not greater than the one on half the line) as a hypothesis.
- **6.29:** to apply a parallelogram overshooting.
- **6.30:** to cut a line in extreme and mean ratio. Euclid applies a parallelogram (6.29) to the square on the line (1.46), and argues with 6.14. Prop. 2.11 cuts a line the same way (Fitzpatrick's note); don't use it in place of his proof.

Risk: high. These are the longest proofs of the book. Split them as Book 4's pentagon was: a lemma for the figure, lemmas for each comparison.

## T10. Props. 6.31–6.33

- **6.31:** in a right-angled triangle, the figure on the hypotenuse equals the similar figures on the sides. State it for the figures T1 defines (triangles at least, as `proposition_31`); Euclid's proof is by 6.8, 6.19 corr. and 5.24. The fourth proportional that 5.24 needs comes from 6.12 for lines, or `Area.fourth` with a comment if the figure gives none.
- **6.32:** triangles with two sides proportional and parallel, placed at an angle, have their third sides in a straight line.
- **6.33:** in equal circles, angles at the centers or at the circumferences are as the circumferences they stand on.
  - Angles need a kind of magnitude. Decide whether `Plane.lean` gets `Angle` like `Length`, and Book 3's arcs `α.arc b c s` an instance as well.
  - Euclid lays off equal circumferences around the circle "any number" of times, and takes their angles together. Past the whole circle, neither the angle nor the circumference is one of System E or Book 3. Find what can be proved faithfully: multiples within the circle, by T2-style induction with Props. 3.26–3.28, and Def. 5.5 over them. If the proposition can't be proved without more, stop and write down what is missing. Don't add axioms.

Risk: high (6.33).

## T11. Primer and docs

- **`Book00/Lean.typ`:** a section on Book 6:
  - ratios of lines and areas in the figure, and T1's notation;
  - similar figures, the squared and compounded ratios;
  - the multiples of T2: induction with System E steps;
  - which facts of the model are used, and where;
  - what is left out or restricted (the figures of 6.18–6.20, 6.31; 6.33).
- **Typesetting:** typeset `Definitions.lean` and `Lemmas.lean` after Book 6's definitions, as Books 4 and 5 do. The subtitle comes from `lean-books`.
- **`CLAUDE.md`:** the Book 6 notes: the two kinds of step, where the definitions are, the facts of the model. Update "Books 1–5".
- **`Roadmap.md`:** delete Milestone 6. Note in Milestone 10 what Book 6 leaves for it.
- **README:** Books 1–6.

## T12. Final check

- `make check` from clean, all books, under the cap. Note the time.
- `tools/gaps.sh N` for N = 1–4 and 6: no failing steps. `Lemmas.lean`, `Definitions.lean` and `Plane.lean` with `systemE.smt` off. `tools/SmtFree.lean`: no theorem with SMT.
- `grep -r sorry lean/Elements lean/SystemE` finds nothing.
- Inspect `ElementsLean.pdf`:
  - the subtitle "Books 1–6";
  - Book 6's title page, definitions and lemmas;
  - the longest proofs (6.20, 6.28, 6.29);
  - the corollaries to 6.8, 6.19 and 6.20.
- `ElementsEnglish.pdf` and `ElementsGreekEnglish.pdf` are unchanged.
- Commit and push.
