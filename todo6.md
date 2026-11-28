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
