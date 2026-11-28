import Elements.Book7.Prop05

namespace Elements.Book7

/-- If `a` is parts of `b`, and `d` is the same parts of `e`, then `a + d` is the same
parts of `b + e`. -/
theorem proposition_6 {a b d e m n : ℕ} (h₁ : PartsOf a b m n) (h₂ : PartsOf d e m n) :
    PartsOf (a + d) (b + e) m n := by
  -- `a` divided into `m` parts `x` of `b`, and `d` into as many parts `y` of `e`
  obtain ⟨hm, hmn, x, rfl, rfl⟩ := h₁
  obtain ⟨-, -, y, rfl, rfl⟩ := h₂
  -- `x + y` is the same part of `b + e` [Prop. 7.5]
  have h := proposition_5 (a := x) (d := y) (n := n) ⟨by omega, rfl⟩ ⟨by omega, rfl⟩
  -- and so for each of the `m` parts
  exact ⟨hm, hmn, x + y, (proposition_5 (n := m) ⟨hm, rfl⟩ ⟨hm, rfl⟩).2, h.2⟩

end Elements.Book7
