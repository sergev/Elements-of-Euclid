# Milestone 5 — Book 5: tasks

Book 5 is Eudoxus's theory of proportion: 25 propositions about magnitudes, their equal multiples, and ratios. It has corollaries to 5.7 and 5.19. Nothing in it is a figure. Euclid's diagrams are straight lines that stand for magnitudes of any kind, so System E is not used.
- 5.1–5.6: multiples.
- 5.7–5.10: same and greater ratios.
- 5.11–5.15: ratios combined.
- 5.16–5.19: alternation, separation, composition, and the remainder.
- 5.20–5.25: ratios via equality (ex aequali), perturbed proportion, and the last two.

The tasks run in order. The common rules in [Roadmap.md](Roadmap.md) apply throughout.

## Routine for every task

- Each task ends with these steps:
  - `make check BOOK=5` and `make` pass;
  - `grep -r sorry lean/Elements/Book5` finds nothing;
  - commit, and remove the task from this file.
- A proposition's `lean/Elements/Book5/PropNN.lean` and its `#lean-proof(...)` line in `Book05/PropNN.typ` go in together.
- Inside `namespace Elements.Book5`, write `Elements.BookN.proposition_M` in full for other books' propositions.
- Keep Lean lines to 90 characters, so that they don't wrap in the PDF.
- Run every check under `systemd-run --user --scope -q -p MemoryMax=6G -p MemorySwapMax=0`. Never use `maxHeartbeats 0`; a finite limit is fine.

How Book 5 differs from Books 1–4:
- **Plain Lean.** The proofs are ordinary Lean with Mathlib tactics (`omega`, `linarith`, `simp`, `abel`), not `euclid_*`. Saturation and SMT play no part, and `tools/gaps.sh` does not apply. `tools/SmtFree.lean` must still list no Book 5 theorem with SMT.
- **Faithfulness.** Euclid proves facts about multiples (5.1–5.6) that Mathlib has as lemmas on `n • a` (`smul_add`, `add_smul`, `mul_smul`).
  - Don't cite those lemmas for a fact Euclid proves. Prove it his way, by induction on the multiple, and cite his proposition from then on.
  - Mathlib's lemmas may be used for what Euclid takes for granted: arithmetic of the counting numbers, and the algebra of addition (C.N. 1–5).
- **No reals, no division.** Ratios are not numbers. "A : B :: C : D" is Def. 5.5, over equimultiples. Don't define a ratio as `a / b`, which would make the book trivial.

## T9. Final check

- `make check` from clean, all books, under the cap. Note the time.
- `tools/gaps.sh N` for N = 1–4: no failing steps. `tools/SmtFree.lean`: no theorem with SMT.
- `grep -r sorry lean/Elements lean/SystemE` finds nothing.
- Inspect `ElementsLean.pdf`:
  - the subtitle "Books 1–5";
  - Book 5's title page and the class;
  - the longest proofs (5.8, 5.17);
  - the corollaries to 5.7 and 5.19.
- `ElementsEnglish.pdf` and `ElementsGreekEnglish.pdf` are unchanged.
- Commit and push.
