# Milestone 4 — Book 4: tasks

Book 4 has 16 propositions, all constructions, plus a corollary to 4.15. They inscribe figures in circles and circumscribe them about circles: triangles (4.2–4.5), squares (4.6–4.9), the regular pentagon (4.11–4.14), the hexagon (4.15) and the fifteen-sided figure (4.16). The golden triangle (4.10) is the key to the pentagon.

The tasks run in order. The common rules in [Roadmap.md](Roadmap.md) apply throughout.

## Routine for every task

- Each task ends with these steps:
  - `make check BOOK=4` and `make` pass;
  - `tools/gaps.sh 4` reports no failing steps;
  - commit, and remove the task from this file.
- A proposition's `lean/Elements/Book4/PropNN.lean` and its `#lean-proof(...)` line in `Book04/PropNN.typ` go in together.
- Inside `namespace Elements.Book4`, write `Elements.BookN.proposition_M` in full whenever Book 4 has its own `proposition_M`.
- Keep Lean lines to 90 characters, so that they don't wrap in the PDF.

Running checks:
- Run every check under `systemd-run --user --scope -q -p MemoryMax=6G -p MemorySwapMax=0`. Never use `maxHeartbeats 0`; a finite limit is fine.
- Keep the file being checked closed in VS Code, whose Lean server runs its own uncapped solvers.
- To find a failing step, run the file with `-Dweak.systemE.smt=false -Dweak.systemE.stats=true`. Each `stats:` line names the step's line and the literal that saturation got stuck on.

Book 1–3 SMT-free rules hold for Book 4: every step closes by saturation. What helped in Book 3:
- **Many points:** split a big figure into lemmas with only the facts they need (as `proposition_4_figure` in Book 2, `proposition_20_lemma` in Book 3). Saturation slows with the number of points.
- **Positions:** Euclid reads positions off the figure. Supply them as steps:
  - `equal_angles` for an angle along a ray;
  - `right_angle_on_lines`, `sum_angles_onlyif`, `on_line_of_eq_angle`;
  - an intersection point, to show which side a point is on.
- **Metric contradictions:** with a goal that is not `False`, add `exfalso` before `euclid_finish`.
- **`∀` facts** (as in internal touching) are not used by saturation; instantiate them: `‹∀ x, …› p`.
- **Squares of lengths:** use `Elements/Book3/Lemmas.lean` (`length_eq_of_square_eq`, `lt_of_square_lt`). Add symmetric asserts when products are written in different orders.
- **Circumferences:** use the Book 3 axioms (`arc_*`), and Props. 3.26–3.30.

## T6. Props. 4.15–4.16: the hexagon and the fifteen-sided figure

- **4.15:** inscribe a regular hexagon: equilateral triangles on the radius. It uses Props. 1.32, 1.13, 1.15, 3.26, 3.29.
  - **Corollary:** the side of the hexagon equals the radius (`proposition_15_corollary`).
  - Euclid's further remarks (circumscribing a hexagon, and a circle in and about it) are said "similarly", without proof. Leave them out, with a comment.
- **4.16:** inscribe a regular fifteen-sided figure, by T1's decision.
  - AC is a side of the inscribed equilateral triangle (4.2), and AB of the pentagon (4.11).
  - The circumference BC is then 2/15 of the whole; bisect it (Prop. 3.30), and the half is a side.
  - Euclid's remark that the rest follow "similarly" (4.1) is left out.
  - With circumferences as magnitudes, the fractions come from the `arc_*` axioms: `arc_add`, `arc_whole`, and equal arcs for equal chords (Prop. 3.28).

## T7. Primer and docs

- **`Book00/Lean.typ`:**
  - how polygons are written: vertices in order, convex;
  - the Book 4 definitions;
  - what is left out: the remarks after 4.15, and the other sides of the fifteen-sided figure.
- **Lemmas:** typeset any `lean/Elements/Book4/Lemmas.lean` after Book 4's definitions, as in Books 2 and 3.
- **`CLAUDE.md`:** the Book 4 notes. **`Roadmap.md`:** delete Milestone 4.
- **README:** Books 1–4.

## T8. Final check

- `make check` from clean, all books, under the cap. Note the time.
- `tools/gaps.sh N` for N = 1–4: no failing steps. `tools/SmtFree.lean`: no theorem with SMT.
- `grep -r sorry lean/Elements lean/SystemE` finds nothing.
- Inspect `ElementsLean.pdf`:
  - the subtitle "Books 1–4";
  - Book 4's title page and lemmas;
  - the longest proofs (4.10, 4.11);
  - the corollary to 4.15.
- `ElementsEnglish.pdf` and `ElementsGreekEnglish.pdf` are unchanged.
- Commit and push.
