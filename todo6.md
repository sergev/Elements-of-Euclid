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

## T1. Definitions and scaffolding

Decide the basis before any proof, and write the decisions in the header comment of `lean/Elements/Book6.lean`.
- **Ratios in the figure.** `Length.of a b h` needs a proof of `a ≠ b`, which makes statements heavy. Decide once how a statement says "AB : CD :: EF : GH" and "△ABC : △DEF :: BC : EF": for example a definition over points that takes the distinctness itself (`∃` or `∀` over the proofs, with a lemma that the choice of proof doesn't matter), or the distinctness as hypotheses. Prove the bridge lemmas it needs: `Length.of` is symmetric and depends only on the length; equal lengths and areas give equal magnitudes; `Area.triangle` doesn't depend on the order of the vertices or on the line.
- **Where the definitions go.** Book 4's definitions are `@[simp] abbrev`s in `SystemE/Book4.lean`, so that saturation sees through them. Those that mention `Proportion` can't go there unless `SystemE` imports Book 5's `Magnitude.lean`. Choose: purely geometric ones (equiangular figures, "same height") in `SystemE/Book6.lean`, and those with ratios in `lean/Elements/Book6/Definitions.lean`; or another split. Record it.
- **Def. 6.1, similar figures.** Equal angles, and the sides about the equal angles proportional. Write it for triangles, quadrilaterals and pentagons (6.18 and 6.20 use a quadrilateral and pentagons), per number of sides like Book 4, with the vertices in corresponding order ("similarly laid down"). Reuse Book 4's `quadrilateral`, `pentagon`, `equiangularTriangles`.
- **Rectilinear figures and their areas.** A figure's area is the sum of the triangles of a fan from one vertex; give quadrilaterals and pentagons an `Area`. Prop. 1.45 makes a parallelogram equal to a quadrilateral, two triangles; check what 6.25, 6.28 and 6.29 need from it.
- **Def. 6.2,** extreme and mean ratio. **Def. 6.3,** height. 6.1 means by "the same height" what its proof uses: the vertices on one line parallel to the bases' line. State it so.
- **Def. 5.9, the squared ratio** (6.19, 6.20, 6.22). `a` has to `c` the squared ratio of `a : b` when `a : b :: b : c`. It is a Book 5 definition: add it to `Magnitude.lean`, with a doc comment, and say in the primer that Book 6 is its first user.
- **The compounded ratio** (6.23). Euclid uses it without a definition in Book 5. Define it as he uses it, through a middle term, with a doc comment that says so.
- **Reciprocal proportion** (6.14, 6.15) is written out in the statements.

Scaffolding:
- `lean/Elements/Book6.lean` with the header comment, imported in `lean/Elements.lean`.
- Add `6` to `lean-books` in `functions.typ`. Check that `ElementsEnglish.pdf` and `ElementsGreekEnglish.pdf` don't change (compare `pdftotext` output).
- Check that `lean/lean4.sublime-syntax` highlights what Book 6 uses (`Length`, `Area`, new definitions). Add what is missing.

## T2. Lemmas: multiples in the figure

6.1 takes "any number" of straight lines equal to the base, and 6.9 a part of a line. Both need equal segments laid off `m` times, for any `m`. That is induction, outside E's style.
- In `lean/Elements/Book6/Lemmas.lean`, by induction on `m : ℕ+`, with each step a System E construction closed by saturation:
  - given `b ≠ c` on a line, a point `g` on the ray beyond `c` with `Length.of b g _ = m • Length.of b c _`, and the `m` points between, each pair the same length apart;
  - triangles with a common vertex on `m` equal consecutive bases: their area is `m •` the area of one (Prop. 1.38 at each step), and the triangle on the whole base has that area.
- Keep each lemma small, taking only the facts it needs, as in Book 4's `Lemmas.lean`.
- Use `Positive.mult_val` only to relate a multiple to a real `m * x` where the induction needs it, with a comment.

Risk: high. If saturation can't close a step of the induction, supply the fact as in Books 1–4 (`between_if`, `sum_areas_if`, …). If System E can't express a step, stop and write down what is missing. Don't add axioms.

## T3. Props. 6.1–6.3: equal heights, parallels, the bisector

- **6.1:** triangles and parallelograms of the same height are as their bases. The bridge to Book 5: the multiples of T2, then Def. 5.5. The parallelograms follow by Prop. 1.34 (double the triangles) and Prop. 5.15, 5.11.
- **6.2:** a parallel to one side cuts the others proportionally, and conversely. Two statements, `proposition_2` and `proposition_2'`.
- **6.3:** the bisector of an angle cuts the base in the ratio of the sides, and conversely.

## T4. Props. 6.4–6.8: similar triangles

- **6.4:** equiangular triangles have proportional sides. Euclid's figure places the triangles side by side; build it.
- **6.5, 6.6, 6.7:** conditions for equiangular triangles. 6.7 has the condition on the remaining angles; state it as Euclid does, both less or both not less than right angles.
- **6.8:** the perpendicular in a right-angled triangle makes triangles similar to the whole and to one another. The corollary (the perpendicular is the mean proportional) is `proposition_8_corollary`.

## T5. Props. 6.9–6.13: constructions

- **6.9:** to cut off a prescribed part of a line: the `m`-th part, by T2.
- **6.10:** to cut a line as a given cut line is cut.
- **6.11, 6.12, 6.13:** third, fourth and mean proportionals.
  - 6.12 constructs the fourth proportional that 5.18 assumes. Where later proofs need one for lines, cite 6.12, not `Length.fourth`.
  - 6.13 uses Prop. 3.31 and the corollary to 6.8.

## T6. Props. 6.14–6.17: reciprocal proportion

- **6.14, 6.15:** equal parallelograms (triangles) with an equal angle have their sides reciprocally proportional, and conversely.
- **6.16, 6.17:** four (three) lines proportional iff the rectangle of the outer equals the rectangle of the middle (the square on the middle).
  - Book 2 writes rectangles as products of lengths. Euclid proves 6.16 from 6.14 with the rectangles drawn: build them (Book 2's `rectangle_on`), relate their areas to the products, and argue with 6.14. Don't replace the proof with `Positive.proportion_of_mul_eq`.

## T7. Props. 6.18–6.22: similar figures

- **6.18:** to describe on a given line a figure similar and similarly laid down to a given one. Do it for a quadrilateral, as in Euclid's figure, and for a triangle; a pentagon if 6.20 needs it.
- **6.19:** similar triangles are in the squared ratio of corresponding sides. The corollary is `proposition_19_corollary`.
- **6.20:** similar polygons divide into similar triangles, and are in the squared ratio of corresponding sides. Pentagons, as in Euclid's figure; say so in the doc comment. The corollary is `proposition_20_corollary`.
- **6.21:** figures similar to the same figure are similar to one another.
- **6.22:** four lines are proportional iff similar figures on them are.

Risk: medium to high. Pentagon proofs carry many facts: build the figure in a lemma and argue in lemmas that take only what they need, as in Book 4.

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
