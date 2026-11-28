import Elements.Book5.Magnitude

namespace Elements.Book5

open Magnitude

variable {M N : Type*} [Magnitude M] [Magnitude N]

/--
Equal magnitudes `A`, `B` have the same ratio to the same `C`, and `C` has the same ratio
to each of them.
-/
theorem proposition_7 {a b : M} (c : M) (h : a = b) :
    Proportion a c b c ∧ Proportion c a c b := by
  -- equal multiples `D`, `E` of `A`, `B` are equal
  have hDE : ∀ m : ℕ+, m • a = m • b := fun m => by rw [h]
  -- so if `D` exceeds a multiple `F` of `C`, `E` exceeds it; if equal, equal; if less,
  -- less; and the same for `F` to `D` and to `E` [Def. 5.5]
  refine ⟨⟨fun m n => ?_, fun m n => ?_, fun m n => ?_⟩,
    ⟨fun m n => ?_, fun m n => ?_, fun m n => ?_⟩⟩ <;> simp only [hDE]

/-- If `A : B :: C : D`, then inversely `B : A :: D : C`. -/
theorem proposition_7_corollary {a b : M} {c d : N} (h : Proportion a b c d) :
    Proportion b a d c where
  gt m n := h.lt n m
  eq m n := eq_comm.trans ((h.eq n m).trans eq_comm)
  lt m n := h.gt n m
