import Elements.Book7.Prop09

namespace Elements.Book7

/--
If `a` is parts of `c`, and `d` is the same parts of `f`, then, alternately, whichever
parts, or part, `a` is of `d`, `c` is the same parts, or part, of `f`: `a ∶ d ∷ c ∶ f`.
-/
theorem proposition_10 {a c d f m n : ℕ} (ha : 0 < a) (hd : 0 < d) (h₁ : PartsOf a c m n)
    (h₂ : PartsOf d f m n) : a ∶ d ∷ c ∶ f := by
  -- `a` divided into the `m` parts `x` of `c`, and `d` into the parts `y` of `f`
  obtain ⟨-, -, x, rfl, rfl⟩ := h₁
  obtain ⟨-, -, y, rfl, rfl⟩ := h₂
  have hx : 0 < x := Nat.pos_of_ne_zero (by rintro rfl; rw [Nat.zero_mul] at ha; omega)
  have hy : 0 < y := Nat.pos_of_ne_zero (by rintro rfl; rw [Nat.zero_mul] at hd; omega)
  -- whichever parts `x` is of `y` (its units), `c` is the same of `f` [Prop. 7.9], and
  -- so is `a` of `d` [Props. 7.5, 7.6]
  refine proportion_iff.mpr ⟨x, y, m, n, hx, hy, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.one_mul] using mul_swap 1 x m
  · simpa only [Nat.one_mul] using mul_swap 1 y m
  · simpa only [Nat.one_mul] using mul_swap 1 x n
  · simpa only [Nat.one_mul] using mul_swap 1 y n

end Elements.Book7
