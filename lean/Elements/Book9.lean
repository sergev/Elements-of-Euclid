import Elements.Book9.Definitions
import Elements.Book9.Lemmas

/-
Book 9: applications of number theory.

Plain Lean over `ℕ`, with Books 7 and 8 (`Elements/Book7.lean`, `Elements/Book8.lean`):
numbers, multiplication (Def. 7.15), proportion (Def. 7.20), continued proportion over
`Fin (n + 1) → ℕ`, and 8.2's `powers`. Book 9 has no definitions of its own; it uses
Book 7's odd and even numbers (Defs. 7.6–7.10) and perfect numbers (Def. 7.22). They are
in `Elements/Book9/Definitions.lean`:
- `EvenNumber a`: divided in half, `a = h + h` (Def. 7.6). `OddNumber a`: not divided in
  half (Def. 7.7). The unit is odd: it is not divided in half, and Euclid's "even or odd"
  (9.30) and his odd multitudes of odd numbers (9.23, 9.29) take it so. Def. 7.7's second
  reading, "differs from an even number by a unit", is the lemma `odd_iff`.
- `EvenTimesEven`, `EvenTimesOdd`, `OddTimesOdd` (Defs. 7.8–7.10): `a = e * f`, measured by
  `e` according to `f`, of the stated kinds. The odd numbers there are numbers, greater
  than the unit: else every even number would be even-times-odd, measured by itself
  according to the unit, and 9.32 would fail. So "an odd half" in 9.33 is an odd number,
  not the unit (`2` is doubled from the unit, not even-times-odd).
- Numbers doubled from a dyad (9.32, 9.36) are `powers 1 2 n`: the unit, the dyad, and so
  on.
- `LeastMeasuredSeq c a`: `c` is the least number measured by `a 0`, …, `a n` (9.14,
  9.20), Book 7's `LeastMeasured` for any multitude.

"Continuously proportional from a unit" is `Continued a` with `a 0 = 1`; `a 1` is "the
number after the unit", and Euclid's "third from the unit" is `a 2`, counting the unit as
first. As in Book 8, any multitude is `Fin (n + 1) → ℕ`, and "similarly" is induction;
where Euclid names three primes or four numbers, the doc comment says so. Squares and
cubes are `a * a`, `a * a * a`. Mathlib's rule is Book 7's: Books 7's and 8's facts are
cited as their propositions; never Mathlib's `Even`, `Odd`, `Nat.Prime`, `Nat.gcd`,
`Nat.Perfect`; linear arithmetic is a common notion, associativity is marked
`-- Missed by Euclid.`, and commutativity is Prop. 7.16.
`Lemmas.lean`: Def. 7.7's second reading, the least number measured by any multitude
(7.34–7.36 by induction), and sums of numbers doubled from the unit.
-/
