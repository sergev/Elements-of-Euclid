import Elements.Book7.Prop16

namespace Elements.Book7

/-- If `a` multiplying `b` and `c` makes `b * a` and `c * a`, these have the same ratio as
`b` and `c`. -/
theorem proposition_17 {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    b ∶ c ∷ b * a ∶ c * a := by
  rcases Nat.lt_or_ge 1 a with ha1 | ha1
  · -- `b` measures `b * a` according to the units in `a` [Def. 7.15], as the unit
    -- measures `a`; so does `c` measure `c * a`: as `b` is to `b * a`, so is `c` to
    -- `c * a` [Def. 7.20]
    have h : b ∶ b * a ∷ c ∶ c * a := Or.inr (Or.inl ⟨a, ⟨ha1, rfl⟩, ⟨ha1, rfl⟩⟩)
    -- alternately [Prop. 7.13]
    exact proposition_13 hb (Nat.mul_pos hb ha) hc (Nat.mul_pos hc ha) h
  · obtain rfl : a = 1 := by omega
    rw [Nat.mul_one, Nat.mul_one]
    exact Proportion.refl hb hc

end Elements.Book7
