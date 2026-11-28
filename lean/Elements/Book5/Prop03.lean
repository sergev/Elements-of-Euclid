import Elements.Book5.Prop02

namespace Elements.Book5

open Magnitude

variable {M : Type*} [Magnitude M]

/--
If a first `A` and a third `C` are equal multiples `m • b`, `m • d` of a second `B` and a
fourth `D`, and equal multiples `EF`, `GH` are taken of the first and the third, `n` times
each, then `EF` and `GH` are equal multiples of the second and the fourth: `n * m` times.
The same holds for `D` as for `B`.
-/
theorem proposition_3 (m n : ℕ+) (b : M) : n • (m • b) = (n * m) • b := by
  -- divide `EF` into `EK`, `KF`, … equal to `A`; each is `m • b`
  induction n using PNat.recOn with
  | one => rw [one_mult, one_mul]
  | succ n ih =>
    -- `EK` and `KF` together are the same multiple of `B` [Prop. 5.2]
    rw [mult_succ, ih, proposition_2, add_mul, one_mul]
