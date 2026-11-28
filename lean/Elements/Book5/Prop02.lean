import Elements.Book5.Prop01

namespace Elements.Book5

open Magnitude

variable {M : Type*} [Magnitude M]

/--
If a first `AB` and a third `DE` are equal multiples `m • c`, `m • f` of a second `C` and
a fourth `F`, and a fifth `BG` and a sixth `EH` are equal multiples `n • c`, `n • f` of
the second and the fourth, then the first and the fifth together, `AG`, and the third and
the sixth together, `DH`, are equal multiples of the second and the fourth: `m + n` times.
The same holds for `F` as for `C`.
-/
theorem proposition_2 (m n : ℕ+) (c : M) : m • c + n • c = (m + n) • c := by
  -- as many magnitudes as are in `AB` and in `BG` equal to `C`, so many are in `AG`
  induction n using PNat.recOn with
  | one => rw [one_mult, mult_succ]
  | succ n ih => rw [mult_succ, ← add_assoc, ih, ← add_assoc, mult_succ]
