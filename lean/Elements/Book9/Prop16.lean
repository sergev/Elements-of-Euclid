import Elements.Book9.Prop15

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/-- If two numbers `a`, `b` are prime to one another, there is no `c` such that as `a` is
to `b`, so `b` is to `c`. `a` is a number, greater than the unit: else
`1 ∶ b ∷ b ∶ b * b`. -/
theorem proposition_16 {a b : ℕ} (ha : 1 < a) (hb : 0 < b) (h : PrimeTo a b) :
    ¬ ∃ c, 0 < c ∧ a ∶ b ∷ b ∶ c := by
  rintro ⟨c, hc, habc⟩
  -- `a`, `b` are the least [Prop. 7.21], so `a` measures `b` [Prop. 7.20]
  obtain ⟨m, hm, -⟩ := Elements.Book7.proposition_20 hb hc (by omega) hb
    (Elements.Book7.proposition_21 (by omega) hb h) habc
  -- and `a` measures itself: it measures `a`, `b`, prime to one another
  have := h a (measures_self a) ⟨m, hm⟩
  omega

end Elements.Book9
