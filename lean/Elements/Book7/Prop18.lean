import Elements.Book7.Prop17

namespace Elements.Book7

/-- If `a` and `b` multiplying `c` make `c * a` and `c * b`, these have the same ratio as
`a` and `b`. -/
theorem proposition_18 {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ∶ b ∷ c * a ∶ c * b := by
  -- `c` multiplying `a` and `b` makes the same numbers [Prop. 7.16]
  rw [proposition_16 ha hc, proposition_16 hb hc]
  -- so they are as `a` to `b` [Prop. 7.17]
  exact proposition_17 hc ha hb

end Elements.Book7
