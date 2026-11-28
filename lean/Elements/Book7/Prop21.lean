import Elements.Book7.Prop20

namespace Elements.Book7

/-- Numbers `a`, `b` prime to one another are the least of those having the same ratio as
them. Stated for the unit as well. -/
theorem proposition_21 {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h : PrimeTo a b) :
    Least a b := by
  -- if not, there are numbers `c₀`, `d₀` less than `a`, `b` in the same ratio
  rintro c₀ d₀ hc₀ hd₀ hcd₀ ⟨hca₀, -⟩
  -- take the least of them -- Missed by Euclid.
  obtain ⟨c, d, hc, hd, hcd', hl, hmin⟩ := exists_least ha hb
  have hca : c < a := Nat.lt_of_le_of_lt (hmin c₀ d₀ hc₀ hd₀ hcd₀) hca₀
  -- `c` measures `a` as many times as `d` measures `b`, `e` times [Prop. 7.20]
  obtain ⟨e, hae, hbe⟩ := proposition_20 ha hb hc hd hl hcd'
  have he : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; rw [Nat.mul_zero] at hae; omega)
  -- so `e` measures `a` according to the units in `c`, and `b` according to the units in
  -- `d` [Prop. 7.16]
  rw [proposition_16 he hc] at hae
  rw [proposition_16 he hd] at hbe
  -- `e` measures `a` and `b`, which are prime to one another: it is the unit
  have := h e ⟨c, hae⟩ ⟨d, hbe⟩
  rw [this, Nat.one_mul] at hae
  omega

end Elements.Book7
