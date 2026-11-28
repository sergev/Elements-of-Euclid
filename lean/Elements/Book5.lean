import Elements.Book5.Magnitude
import Elements.Book5.Prop01
import Elements.Book5.Prop02
import Elements.Book5.Prop03
import Elements.Book5.Prop04
import Elements.Book5.Prop05
import Elements.Book5.Prop06

/-
Book 5: proportion, Eudoxus's theory of the ratios of magnitudes.

Book 5 is not about figures. Euclid's lines stand for magnitudes of any kind, so System E
is not used: the proofs are plain Lean. The basis, in `Elements/Book5/Magnitude.lean`:
- Magnitudes. `Magnitude M` is a kind of magnitude: Mathlib's `AddCommSemigroup` (an
  associative and commutative addition, without zero) and a linear order, with three
  laws of our own: a magnitude is less than its sum with another (so none is zero), the
  lesser taken from the greater leaves a remainder, and Def. 5.4. Mathlib's ordered
  monoids are not used: they bring `0`, and their lemmas on `n • a` would do Euclid's
  work. The order lemmas for addition (C.N. 1–5) are Mathlib's, from instances proved
  from the laws.
- Multiples. `n • a` with `n : ℕ+` is `a` taken `n` times, our own; Mathlib knows nothing
  of it. A multiple of a sum, a sum of multiples and a multiple of a multiple are
  Props. 5.1–5.3, proved by induction on the multiple. What Euclid takes for granted of
  multiples (equal multiples of equals are equal, the greater multiple is greater) is
  proved once in `Magnitude.lean`.
- Def. 5.4 (Archimedes): a multiple of each magnitude exceeds any other of its kind. It
  is a field of the class, since Euclid uses it of any two magnitudes of one kind (5.8).
- Def. 5.5, `Proportion a b c d`, "a : b :: c : d": equal multiples of the first and the
  third both exceed, are both equal to, or are both less than equal multiples of the
  second and the fourth. `a`, `b` are of one kind `M`, and `c`, `d` of a kind `N`, the
  same or another. Ratios are not numbers: there are no reals and no division.
- Def. 5.7, `GreaterRatio a b c d`: for some equimultiples, the multiple of the first
  exceeds that of the second, and the multiple of the third does not exceed that of the
  fourth. A lesser ratio is a greater one read the other way.
- Defs. 5.12–5.18 (alternate, inverse, composition, separation, conversion, ex aequali,
  perturbed proportion) are ways of forming a proportion; the statements write them out.
- Any number of magnitudes (5.1, 5.12, 5.22) is a function `a : Fin (n + 1) → M`, the
  magnitudes `a 0`, …, `a n`, and `sum a` is all of them added. Euclid argues with two or
  three; the proofs go by induction on `n`, with his case as the step.
- Prop. 5.18 assumes that a fourth proportional exists. It does not follow from the laws
  of magnitudes, so 5.18 (and 5.24, which uses it) take it as a hypothesis, marked in the
  proof. Book 6 constructs it for lines (Prop. 6.12).
-/
