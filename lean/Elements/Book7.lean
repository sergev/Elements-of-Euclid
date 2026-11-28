import Elements.Book7.Definitions
import Elements.Book7.Lemmas
import Elements.Book7.Prop01
import Elements.Book7.Prop02
import Elements.Book7.Prop03
import Elements.Book7.Prop04
import Elements.Book7.Prop05
import Elements.Book7.Prop06
import Elements.Book7.Prop07
import Elements.Book7.Prop08
import Elements.Book7.Prop09
import Elements.Book7.Prop10

/-
Book 7: numbers.

Book 7 is about numbers, not figures, so System E is not used: the proofs are plain Lean
over `ℕ`, as Book 5's are over magnitudes. The basis, in
`Elements/Book7/Definitions.lean`:
- Numbers (Defs. 7.1, 7.2). A number is a multitude of units, `1 < a`; the unit is `1`.
  Euclid's arguments often admit the unit (a quotient that may be one, "as many units
  as"), so a statement takes `0 < a` where its proof does not need more, and its doc
  comment says so.
- Multiplication (Def. 7.15). `a * b` is `a` added to itself as many times as there are
  units in `b`: "`b` multiplies `a`", and "`a` multiplying `b` makes `c`" is `c = b * a`.
  It is Lean's own `*`, so `a * (b + 1) = a * b + a` (`Nat.mul_succ`) is the definition.
  Counted as the definition too: `Nat.mul_zero`, `Nat.mul_one`, `Nat.one_mul` (the unit
  taken `b` times is `b`, Def. 7.2), `Nat.mul_add` and `Nat.mul_sub` (`a` taken `b` and
  `c` times). Not counted: `Nat.add_mul` (that is Prop. 7.5), `Nat.mul_comm` (7.16), and
  `ring`, which uses it. The order and cancellation of multiples (more times is more,
  equal multiples of unequals are unequal) are common notions.
- Measuring (Defs. 7.3–7.5). "`a` measures `b` according to the units in `c`" is
  `b = a * c`, and "`a` measures `b`" is Mathlib's `a ∣ b`, which says just that. Part
  (`PartOf a b n`, `b = a * n`) and parts (`PartsOf a b m n`, `a = e * m`, `b = e * n`)
  name the numbers that make them the same: the same `n`, or the same `m` and `n`.
- Proportion (Def. 7.20), `a ∶ b ∷ c ∶ d`: the first is the same multiple, part, or parts
  of the second that the third is of the fourth, and, where the first is greater, the
  second the same parts of the first. It is neither Book 5's proportion nor
  `a * d = b * c` (Prop. 7.19). `proportion_iff` puts the cases together, `Lemmas.lean`.
- Primes, numbers prime to one another, composite, plane, solid, square, cube, similar and
  perfect numbers (Defs. 7.11–7.14, 7.16–7.19, 7.21, 7.22) are `def`s. Odd and even
  (Defs. 7.6–7.10) are left to Book 9.
- Any multitude of numbers (7.12, 7.14, 7.33) is `Fin (n + 1) → ℕ`, as in Book 5, and so
  in Books 8 and 9. Where Euclid takes three numbers (7.3, 7.36), the statement is for
  three.

What is taken from Mathlib, `Lemmas.lean`:
- the common notions of measuring (Fitzpatrick's notes to 7.1), proved from the
  definition of multiplication;
- Book 5 in Book 7: Euclid cites Props. 5.7, 5.9 (7.19) and 5.13 (7.33), and uses 5.11
  throughout, of numbers. Def. 7.20 does not give them: `4 ∶ 6` is the same parts as
  `2 ∶ 3` only in least terms. They are proved from the model, four numbers being
  proportional when `a * d = b * c`, by Mathlib's arithmetic, and marked
  `-- Missed by Euclid.`;
- what Book 7 proves is never taken from Mathlib before it is proved: the greatest common
  measure (`Nat.gcd`), commutativity (7.16), cross-multiplication (7.19), numbers prime
  to one another (`Nat.Coprime`), primes (`Nat.Prime`) and the least common multiple
  (`Nat.lcm`). Once proved, the proposition (or the Mathlib lemma that says the same) is
  cited with a comment naming it. Associativity of multiplication, which Euclid uses
  without proof, is Mathlib's `Nat.mul_assoc`, marked `-- Missed by Euclid.`
-/
