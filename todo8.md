# Milestone 8 — Book 8: tasks

Book 8 is about numbers in continued proportion: 27 propositions, with a corollary to 8.2. It has no definitions of its own. It uses Book 7's (Defs. 7.15, 7.20, 7.21) and Book 5's squared and cubed ratio (Defs. 5.9, 5.10), applied to numbers.
- 8.1–8.4: the least numbers in continued proportion.
- 8.5–8.7: plane numbers in the compounded ratio; measuring in continued proportion.
- 8.8–8.10: numbers falling between in continued proportion.
- 8.11–8.13: mean proportionals between squares and between cubes; powers of proportionals.
- 8.14–8.17: squares and cubes measuring one another, and their sides.
- 8.18–8.21: similar plane and solid numbers and their means.
- 8.22–8.27: squares and cubes in continued proportion, and in the ratio of squares or cubes.

The tasks run in order, after Milestone 7. The common rules in [Roadmap.md](Roadmap.md) apply throughout, and so does Milestone 8 there.

## Routine for every task

- Each task ends with these steps:
  - `make check BOOK=8` and `make` pass;
  - `grep -r sorry lean/Elements/Book8` finds nothing;
  - commit, and remove the task from this file.
- A proposition's `lean/Elements/Book8/PropNN.lean` and its `#lean-proof(...)` line in `Book08/PropNN.typ` go in together.
- Inside `namespace Elements.Book8`, write `Elements.BookN.proposition_M` in full for other books' propositions.
- Keep Lean lines to 90 characters, so that they don't wrap in the PDF.
- Run every check under `systemd-run --user --scope -q -p MemoryMax=6G -p MemorySwapMax=0`. Never use `maxHeartbeats 0`; a finite limit is fine.

How Book 8 differs from Book 7:
- **Same basis.** Plain Lean over `ℕ`, with Book 7's definitions: numbers, multiplication (Def. 7.15), proportion (Def. 7.20), similar plane and solid numbers (Def. 7.21). The Mathlib rule of Milestone 7 holds.
  - Book 7's facts are cited as Book 7's propositions, not as their Mathlib equivalents.
  - Linear arithmetic (`omega`, `linarith`) is a common notion.
  - Associativity of multiplication is marked `-- Missed by Euclid.` as in Book 7.
- **Arbitrary lengths.** Euclid argues with three or four named numbers, then says "similarly". The statements are for any multitude, so the proofs are by induction.
  - The induction follows Euclid's step: what he does for `A`, `B`, `C`, done once more.
  - Where Euclid states only three or four numbers, the doc comment says so. A general statement is still preferred when the induction is natural.
- **Squares and cubes.** A square is a number multiplying itself, `a * a`; a cube is `a * a * a` (Defs. 7.18, 7.19). Don't use `^`.

## T10. Final check

- `make check` from a clean build, all books, under the cap. Note the time.
- `tools/gaps.sh N` for N = 1–4 and 6: no failing steps. `tools/SmtFree.lean`: no theorem with SMT.
- `grep -r sorry lean/Elements lean/SystemE` finds nothing.
- `grep -rn "Nat.gcd\|Nat.lcm\|Nat.Coprime\|Nat.Prime\|\^" lean/Elements/Book8`: each hit is allowed by Milestone 7's rule, with a comment.
- Inspect `ElementsLean.pdf`:
  - the subtitle "Books 1–8";
  - Book 8's title page, definitions and lemmas;
  - the inductive proofs (8.2, 8.8, 8.13);
  - the corollary to 8.2, and 8.20.
- `ElementsEnglish.pdf` and `ElementsGreekEnglish.pdf` are unchanged.
- Commit and push.
