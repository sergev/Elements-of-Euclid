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

## T4. Props. 8.8–8.10: numbers falling between

- **8.8:** as many numbers fall between two numbers in continued proportion, so many between any two in the same ratio.
- **8.9:** if two numbers prime to one another have numbers falling between them, as many fall between each of them and the unit.
  - The unit is in the sequence. Check that T1's continued proportion allows it, since the unit is not a number (Def. 7.2).
- **8.10:** the converse: between each of two numbers and the unit, so many between the two.

## T5. Props. 8.11–8.13: means between squares and cubes

- **8.11:** one mean proportional falls between two squares, and square has to square the squared ratio of side to side.
- **8.12:** two mean proportionals fall between two cubes, and the cubed ratio of side to side.
- **8.13:** the squares of continuous proportionals are continuous proportionals, and so are their cubes. Euclid does three numbers and says "similarly"; prove it for any multitude.

## T6. Props. 8.14–8.17: squares and cubes measuring

- **8.14, 8.15:** a square (cube) measures a square (cube) exactly when the side measures the side. Two directions each.
- **8.16, 8.17:** the same with "does not measure" (the contrapositives, as Euclid proves them).

## T7. Props. 8.18–8.21: similar plane and solid numbers

- **8.18:** one mean proportional falls between similar plane numbers, and plane has to plane the squared ratio of corresponding sides.
- **8.19:** two between similar solid numbers, and the cubed ratio.
- **8.20, 8.21:** the converses: if one (two) mean proportionals fall between two numbers, they are similar plane (solid) numbers.
  - Fitzpatrick notes that 8.20's proof is defective: it does not show that `F × E = C`. Prove that step and mark it `-- Missed by Euclid.`
  - The step that shows `D : E :: A : C` is not needed, since that is a hypothesis; say so in a comment and skip it.

## T8. Props. 8.22–8.27: squares and cubes in ratios

- **8.22, 8.23:** of three (four) continuous proportionals, if the first is a square (cube), so is the third (fourth). Through 8.20 (8.21) and 7.22-type steps.
- **8.24, 8.25:** two numbers in the ratio of a square to a square (cube to cube), the first a square (cube): so is the second.
- **8.26, 8.27:** similar plane (solid) numbers are in the ratio of a square to a square (cube to cube).

## T9. Primer and docs

- **`Book00/Lean.typ`:** a section on Book 8:
  - continued proportion and the "any multitude" representation;
  - how Euclid's "similarly" becomes induction;
  - the squared, cubed and compounded ratios of numbers, carried over from Books 5 and 6;
  - the gap in 8.20.
- **`CLAUDE.md`:** Book 8 notes: the basis, the representation, where the definitions are. Update "Books 1–7".
- **`Roadmap.md`:** delete Milestone 8. Record in Milestone 9 what Book 9 inherits: continued proportion from a unit, squares and cubes, the step lemmas.
- **README:** Books 1–8.

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
