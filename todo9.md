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

## T2. Props. 9.1–9.7: products of similar plane numbers, squares and cubes

- **9.1:** similar plane numbers multiplied make a square, through 8.18, 8.8 and 8.22. Take the sides as Book 8 does (8.18): products with `c ∶ d ∷ e ∶ f`.
- **9.2:** the converse: if two numbers multiplied make a square, they are similar plane numbers, through 8.20. As in 8.20, the sides may be the unit; state it with positive sides.
- **9.3–9.6:** a cube multiplying itself, or another cube, makes a cube (9.3, 9.4). If a cube multiplied by a number makes a cube, the number is a cube (9.5). If a number multiplied by itself makes a cube, it is a cube (9.6). These go through 8.19, 8.8 and 8.23. 8.23 takes four numbers with `1 < d`; keep track of where the unit could appear.
- **9.7:** a composite number multiplying any number makes a solid number. Def. 7.17 needs all three sides greater than the unit, so the number multiplied must be one too.

Risk: low.

## T3. Props. 9.8–9.13: continued proportion from a unit

- **9.8:** from a unit, the third and every second after it are squares, the fourth and every third after it are cubes, and the seventh and every sixth after it are both. State it with indices: `a (2 * k)` is a square, `a (3 * k)` a cube. Euclid shows the first few and says "similarly"; prove it for every `k`.
- **9.9:** if `a 1` is a square (cube), all are squares (cubes).
- **9.10:** if `a 1` is not a square, the squares are `a (2 * k)` alone; and the same for cubes, with `a (3 * k)`. The cube half goes through 8.25 and 9.6.
- **9.11:** a lesser number measures a greater according to one of the proportionals, through 7.15. **9.11 corollary:** the number by which it measures is as far from the measured as the measuring is from the unit. State both by index: `a j = a i * a (j - i)`.
- **9.12:** every prime measuring the last also measures `a 1`, through 7.29, 9.11 and 7.20. Euclid's proof is by contradiction, and long.
- **9.13:** if `a 1` is prime, the last is measured by none except the proportionals. This is used by 9.32 and 9.36, so state it in the form they need: every number measuring `a n` is some `a i`.

Risk: medium. The index arithmetic over `Fin (n + 1)` (`a (2 * k)` needs `2 * k ≤ n`) is the main cost: state it with `Fin` subscripts built from `Nat` indices, as 8.6 does.

## T4. Props. 9.14–9.20: primes and proportionals

- **9.14:** a least number measured by primes is measured by no other prime, through 7.30. Euclid takes three primes; state it for any multitude, with T1's least number measured.
- **9.15:** if three continuous proportionals are the least in their ratio, any two added together are prime to the third.
  - Euclid cites Props. 2.3 and 2.4 for numbers. Book 2's are about lines. Prove the identities by Book 7's multiplication (7.5, and 7.16 with a comment), and cite Book 2 in the comment.
  - Fitzpatrick notes a gap: if `αβ` measures `α² + β² + 2αβ`, it also measures `α² + β² + αβ`. Prove it and mark it `-- Missed by Euclid.`
- **9.16, 9.17:** if two numbers are prime to one another (if the outermost of continuous proportionals are), there is no third (fourth) proportional in that ratio.
- **9.18:** a third proportional to `a`, `b` exists exactly when `a` measures `b * b`. State it as an `↔`.
- **9.19:** a fourth proportional to `a`, `b`, `c` exists exactly when `a` measures `b * c`.
  - Euclid's case analysis is defective. In his second case, "not continuously proportional, outermost prime: impossible", the proof assumes a fifth proportional `E` exists. It is false: `2`, `4`, `3` have the fourth proportional `6`.
  - State the true criterion as an `↔`, prove it as his last cases do (7.19), and say in the doc comment which of his cases fail.
- **9.20:** there are more primes than any assigned multitude.
  - Euclid takes three primes and the least number they measure (7.36), plus the unit. State it for any multitude, `p : Fin (n + 1) → ℕ`: some prime is none of them.
  - Use T1's least number measured, and 7.31, 7.28 as Euclid does. Euclid's "either prime or not" is two cases.

Risk: medium, for 9.12–9.15 and 9.19.

## T5. Props. 9.21–9.29: odd and even

- **9.21–9.23:** a sum of evens is even; a sum of an even multitude of odds is even; of an odd multitude, odd. Over Book 7's `sum`, by induction. The multitude is `n + 1`.
- **9.24–9.27:** differences of even and odd, with the subtracted number less (or not greater). Euclid uses the unit ("differs by a unit"), so Def. 7.7's second reading is used here.
- **9.28, 9.29:** an odd number multiplying an even makes an even; multiplying an odd makes an odd, through 9.21 and 9.23 (the product is a sum of as many equals, Def. 7.15).

Risk: low. Keep the proofs Euclid's: 9.21 from the halves, not `omega` on the conclusion.

## T6. Props. 9.30–9.34: odd measuring even; even-times-even and even-times-odd

- **9.30:** an odd number measuring an even measures its half, through 9.23.
- **9.31:** an odd number prime to a number is prime to its double, through 9.30.
- **9.32:** numbers doubled from a dyad are even-times-even only, through 9.13. "Only" means not even-times-odd.
- **9.33:** a number with an odd half is even-times-odd only.
- **9.34:** a number neither doubled from a dyad nor with an odd half is both.
  - Euclid's first step, "even-times-even, for it does not have an odd half", reads Def. 7.8 differently from 7.8 as stated. Check it against T1's definition, and prove the step or mark it `-- Missed by Euclid.`
  - The number must be even (Euclid assumes it); make that a hypothesis.
  - "Cut in half continually" is a descent: an induction on the number, as in 7.31.

Risk: medium, because of the definitions. Settle T1's choices before this.

## T7. Props. 9.35–9.36: the sum of a continued proportion; perfect numbers

- **9.35:** for continuous proportionals, as the excess of the second over the first is to the first, so the excess of the last over the first is to the sum of all before it. Euclid's proof is through separation (7.11, 7.13) and 7.12, over any multitude. The numbers increase ("beginning from the least"), so the subtractions are in `ℕ`.
- **9.36:** if the sum of the unit and the numbers doubled from it is prime, that sum times the last is perfect (Def. 7.22).
  - Book 7's `Perfect` is the sum of `(List.range a).filter (· ∣ a)`. Euclid shows that the number is the sum of the numbers he names, and that it is measured by no others (9.13, 7.19, 7.20).
  - Connecting those parts with the filtered list is the work: prove a lemma in `Lemmas.lean` that the parts of `a` are exactly a given list of distinct numbers, then the sums agree.
  - Euclid's "measured by no other" is by contradiction through 7.19 and 7.20; keep it.

Risk: high for 9.36 (the bridge to `Perfect`); low for 9.35.

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
