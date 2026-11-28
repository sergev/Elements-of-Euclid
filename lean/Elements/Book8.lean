import Elements.Book8.Definitions
import Elements.Book8.Lemmas
import Elements.Book8.Prop01
import Elements.Book8.Prop02
import Elements.Book8.Prop03
import Elements.Book8.Prop04

/-
Book 8: numbers in continued proportion.

Like Book 7, plain Lean over `ℕ`, with Book 7's basis (`Elements/Book7.lean`): numbers,
multiplication (Def. 7.15), measuring, proportion (Def. 7.20), plane, solid, square, cube
and similar numbers (Defs. 7.16–7.19, 7.21). Book 8 has no definitions of its own; the
phrases of its enunciations are in `Elements/Book8/Definitions.lean`:
- Any multitude of numbers is `Fin (n + 1) → ℕ`, as in Book 7. `ContinuedIn a r s`: each
  is to the next as `r` to `s`; `Continued a`: as the first to the second. The unit may be
  among them (8.9, 8.10, and Book 9's numbers continuously proportional from a unit).
- `SameRatios b a`, each to the next as each to the next; `LeastSeq a`, the least having
  the same ratios as them, as Book 7's `Least` for two: no numbers in the same ratios are
  each less than each.
- `FallBetween n a b`: `n` numbers fall between `a` and `b` in continued proportion. The
  same `n` is Euclid's "as many …, so many" (8.8–8.10).
- `SquaredRatio`, `CubedRatio`: Defs. 5.9, 5.10, carried over to numbers by Euclid
  without comment, with proportion of numbers (Def. 7.20) and the middle terms between the
  two numbers. `CompoundRatio`: through a middle term, as Euclid builds it in 8.5.

Euclid argues with three or four named numbers and says "similarly". The statements are
for any multitude, and the proofs are by induction, each step being what Euclid does for
`A`, `B`, `C`, done once more; where he states only three or four numbers, the doc
comment says so. A square is `a * a`, a cube `a * a * a` (Defs. 7.18, 7.19), never `^`.
Mathlib's rule is Book 7's: Book 7's facts are cited as its propositions, linear
arithmetic is a common notion, associativity is marked `-- Missed by Euclid.`
`Lemmas.lean`: ex aequali along a sequence (Prop. 7.14 a step at a time), and the least
numbers in the same ratios being equal.
-/
