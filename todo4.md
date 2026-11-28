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
