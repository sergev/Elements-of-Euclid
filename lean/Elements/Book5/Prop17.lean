import Elements.Book5.Prop01
import Elements.Book5.Prop02

namespace Elements.Book5

open Magnitude

variable {M N : Type*} [Magnitude M] [Magnitude N]

/--
`HK` taken away from `GK` and from `HO`: `GK` exceeds `HO`, is equal to it, or is less,
as `GH` does `KO`.
-/
theorem proposition_17_lemma (x y z : M) :
    (z + y < x + z ↔ y < x) ∧ (x + z = z + y ↔ x = y) ∧ (x + z < z + y ↔ x < y) := by
  rw [add_comm x z]
  exact ⟨add_lt_add_iff_left z, add_right_inj z, add_lt_add_iff_left z⟩

/--
If composed magnitudes are proportional, `AB : BE :: CD : DF`, then they are also
proportional separated, `AE : EB :: CF : FD`. `AB` is `AE` and `EB`, `CD` is `CF` and
`FD`.
-/
theorem proposition_17 {a b : M} {c d : N} (h : Proportion (a + b) b (c + d) d) :
    Proportion a b c d := by
  -- let `GH`, `HK`, `LM`, `MN` be equal multiples `m` of `AE`, `EB`, `CF`, `FD`, and
  -- `KO`, `NP` other equal multiples `n` of `EB`, `FD`
  refine ⟨fun m n => ?_, fun m n => ?_, fun m n => ?_⟩
  -- `GK`, `LN` are equal multiples of `AB`, `CD` [Prop. 5.1], and `HO`, `MP`, added
  -- together, of `EB`, `FD` [Prop. 5.2]; so `GK`, `HO` and `LN`, `MP` exceed together,
  -- are equal together, are less together [Def. 5.5]
  · have h₁ := h.gt m (m + n)
    rw [← proposition_1', ← proposition_1', ← proposition_2, ← proposition_2] at h₁
    -- take `HK` away from `GK` and `HO`, and `MN` from `LN` and `MP`
    rwa [(proposition_17_lemma _ _ _).1, (proposition_17_lemma _ _ _).1] at h₁
  · have h₁ := h.eq m (m + n)
    rw [← proposition_1', ← proposition_1', ← proposition_2, ← proposition_2] at h₁
    rwa [(proposition_17_lemma _ _ _).2.1, (proposition_17_lemma _ _ _).2.1] at h₁
  · have h₁ := h.lt m (m + n)
    rw [← proposition_1', ← proposition_1', ← proposition_2, ← proposition_2] at h₁
    rwa [(proposition_17_lemma _ _ _).2.2, (proposition_17_lemma _ _ _).2.2] at h₁
