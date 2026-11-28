import Elements.Book7.Prop37

namespace Elements.Book7

/-- If `a` has a part `b`, called the same as `c` (the `c`th part), then `c` measures
`a`. -/
theorem proposition_38 {a b c : ℕ} (hb : 0 < b) (h : PartOf b a c) : c ∣ a := by
  obtain ⟨hc, ha⟩ := h
  -- the unit is the `c`th part of `c`, as `b` of `a`: the unit measures `c` as many times
  -- as `b` measures `a`; alternately, the unit measures `b` as many times as `c` measures
  -- `a` [Prop. 7.15]
  obtain ⟨m, -, ha'⟩ := proposition_15 hb (by omega) (Nat.one_mul c).symm ha
  exact ⟨m, ha'⟩

end Elements.Book7
