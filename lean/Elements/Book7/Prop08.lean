import Elements.Book7.Prop07

namespace Elements.Book7

/-- If `a` is those parts of `b` that `e` taken away is of `f` taken away, then the
remainder `a - e` is the same parts of the remainder `b - f`. -/
theorem proposition_8 {a b e f m n : ℕ} (h₁ : PartsOf a b m n) (h₂ : PartsOf e f m n)
    (hea : e ≤ a) : PartsOf (a - e) (b - f) m n := by
  -- `a` divided into the `m` parts `x` of `b`, and `e` into the parts `y` of `f`
  obtain ⟨hm, hmn, x, rfl, rfl⟩ := h₁
  obtain ⟨-, -, y, rfl, rfl⟩ := h₂
  -- `b` is greater than `f`, so `x` is greater than `y`
  have hyx : y ≤ x := by
    by_contra h
    have := Nat.mul_lt_mul_of_pos_right (Nat.lt_of_not_le h) (by omega : m > 0)
    omega
  -- the remainder `x - y` is the same part of the remainder `b - f` [Prop. 7.7]
  have h := proposition_7 (n := n) ⟨by omega, rfl⟩ ⟨by omega, rfl⟩ hyx
  -- and the `m` remainders are together `a - e` [Prop. 7.5]
  have h' := (proposition_5 (a := y) (d := x - y) ⟨hm, rfl⟩ ⟨hm, rfl⟩).2
  rw [Nat.add_sub_cancel' hyx] at h'
  exact ⟨hm, hmn, x - y, by omega, h.2⟩

end Elements.Book7
