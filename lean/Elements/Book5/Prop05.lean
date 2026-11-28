import Elements.Book5.Prop01

namespace Elements.Book5

open Magnitude

variable {M : Type*} [Magnitude M]

/--
If a magnitude `AB` is the same multiple `m` of a magnitude `CD` that `AE`, taken away, is
of `CF`, taken away, then the remainder `EB` is the same multiple of the remainder `FD`.
`AB` is `AE` and `EB`, `a + b`; `CD` is `CF` and `FD`, `c + d`.
-/
theorem proposition_5 (m : ℕ+) {a b c d : M} (h : a + b = m • (c + d)) (h' : a = m • c) :
    b = m • d := by
  -- Euclid makes `EB` the same multiple of some `CG` as `AE` is of `CF`. That divides
  -- `EB` into `m` equal parts, which the laws of magnitudes do not give. As Simson does,
  -- make the same multiple of `FD` instead.
  -- `AE` and it are the same multiple of `CF` and `FD` together, `CD` [Prop. 5.1]
  have h₁ : a + m • d = m • (c + d) := by rw [h', proposition_1']
  -- so they are equal to `AB`; take away `AE` from both
  exact (add_left_cancel (h₁.trans h.symm)).symm
