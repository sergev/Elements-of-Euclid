# Milestone 9 — Book 9: tasks

Book 9 completes the arithmetic books: 36 propositions, with a corollary to 9.11. It has no definitions of its own. It uses Book 7's: odd and even numbers (Defs. 7.6–7.10, which Book 7 left to Book 9), perfect numbers (Def. 7.22), and Book 8's continued proportion.
- 9.1–9.7: products of similar plane numbers, of squares and of cubes.
- 9.8–9.13: numbers continuously proportional from a unit.
- 9.14–9.20: primes, and third and fourth proportionals; the infinitude of primes (9.20).
- 9.21–9.29: sums, differences and products of odd and even numbers.
- 9.30–9.34: odd measuring even; even-times-even and even-times-odd numbers.
- 9.35–9.36: the sum of a continued proportion; perfect numbers.

The tasks run in order, after Milestone 8. The common rules in [Roadmap.md](Roadmap.md) apply throughout, and so does Milestone 9 there.

## Routine for every task

- Each task ends with these steps:
  - `make check BOOK=9` and `make` pass;
  - `grep -r sorry lean/Elements/Book9` finds nothing;
  - commit, and remove the task from this file.
- A proposition's `lean/Elements/Book9/PropNN.lean` and its `#lean-proof(...)` line in `Book09/PropNN.typ` go in together.
- Inside `namespace Elements.Book9`, write `Elements.BookN.proposition_M` in full for other books' propositions.
- Keep Lean lines to 90 characters, so that they don't wrap in the PDF.
- Run every check under `systemd-run --user --scope -q -p MemoryMax=6G -p MemorySwapMax=0`. Never use `maxHeartbeats 0`; a finite limit is fine.

How Book 9 differs from Book 8:
- **Same basis.** Plain Lean over `ℕ`, with Books 7 and 8: numbers, multiplication (Def. 7.15), proportion (Def. 7.20), continued proportion over `Fin (n + 1) → ℕ`, `powers`, and the step lemmas listed in Milestone 9. The Mathlib rule of Milestone 7 holds.
  - Book 7's and Book 8's facts are cited as their propositions, not as their Mathlib equivalents. Never `Nat.gcd`, `Nat.Coprime`, `Nat.Prime`, `Nat.lcm`, and never Mathlib's `Even`, `Odd`, `Nat.Perfect`, `Nat.divisors`.
  - Linear arithmetic (`omega`) is a common notion. Associativity is marked `-- Missed by Euclid.`; commutativity is Prop. 7.16, cited with a comment.
  - Mathlib is built here only for what is already imported: no `Fin.snoc`, `![…]` or `linarith`. Use `Fin.lastCases`, Book 8's `three`/`four`, and rewriting.
- **Arbitrary lengths.** As in Book 8, "any multitude" is `Fin (n + 1) → ℕ`, and "similarly" is induction. Where Euclid names three primes (9.14, 9.20) or four numbers, the statement is for any multitude, and the doc comment says what Euclid takes.
- **From a unit.** "Continuously proportional, from a unit" is `Continued a` with `a 0 = 1`; `a 1` is "the number after the unit", and Euclid's "third from the unit" is `a 2`, counting the unit as first. `eq_powers_one` (Book 8, Prop. 8.10) makes such numbers `powers 1 (a 1)`.
- **Squares and cubes.** `a * a`, `a * a * a`, never `^`. `SquareNumber`, `CubeNumber` need the side greater than the unit; where the side may be the unit (as in 8.20), state the product with positive sides, and say so.

## T8. Primer and docs

- **`Book00/Lean.typ`:** a section on Book 9:
  - odd and even and the kinds of even numbers, and the choices of T1;
  - continued proportion from a unit, and the index statements of 9.8–9.13;
  - the defect in 9.19, and the steps marked missed (9.15, 9.34);
  - how 9.36 reaches Def. 7.22.
- **`CLAUDE.md`:** Book 9 notes: the definitions and where they are, "from a unit", the least number measured by any multitude. Update "Books 1–8".
- **`Roadmap.md`:** delete Milestone 9, and update the table and the opening paragraph. Record in Milestone 10 what Book 10 inherits from the number books: numbers in the ratio of a square to a square (8.24, 8.26, 9.1, 9.2) for 10.9 and the lemmas before 10.29.
- **README:** Books 1–9.

## T9. Final check

- `make check` from a clean build (remove `lean/.lake/build` only), all books, under the cap. Note the time.
- `tools/gaps.sh N` for N = 1–4 and 6: no failing steps. `tools/SmtFree.lean`: no theorem with SMT.
- `grep -r sorry lean/Elements lean/SystemE` finds nothing.
- `grep -rn "Nat.gcd\|Nat.lcm\|Nat.Coprime\|Nat.Prime\|Even\b\|Odd\b\|\^" lean/Elements/Book9`: each hit is our own definition, or allowed by Milestone 7's rule with a comment.
- Inspect `LeanElementsOfEuclid.pdf`:
  - the subtitle "Books 1–9";
  - Book 9's title page, definitions and lemmas;
  - 9.8, 9.11 and its corollary, 9.19, 9.20 and 9.36.
- `ElementsEnglish.pdf` and `ElementsGreekEnglish.pdf` are unchanged.
- Delete this file, and commit.
