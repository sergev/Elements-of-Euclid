import Elements.Book9.Prop04

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/-- If a cube number `a` multiplying some number `b` makes a cube number, the number
multiplied is cube. `b` is a number, greater than the unit. -/
theorem proposition_5 {a b : ℕ} (hb : 1 < b) (ha : CubeNumber a)
    (hc : CubeNumber (b * a)) : CubeNumber b := by
  have hd := proposition_3 ha
  have ha' := ha
  obtain ⟨p, hp, rfl⟩ := ha
  obtain ⟨q, hq, hcq⟩ := hc
  obtain ⟨r, hr, hdr⟩ := hd
  have ha0 := one_lt_cube hp
  -- let `a` multiplying itself make `d`, cube [Prop. 9.3]; as `a` is to `b`, so `d` is to
  -- `c` [Prop. 7.17]
  have h17 := Elements.Book7.proposition_17 (by omega) (by omega) (by omega)
    (a := p * p * p) (b := p * p * p) (c := b)
  -- `d`, `c` are cube, so similar solid numbers: two numbers fall between them
  -- [Prop. 8.19]
  have h19 := fallBetween_cubes (show 0 < r by omega) (show 0 < q by omega)
  rw [← hdr, ← hcq] at h19
  -- as `d` is to `c`, so `a` is to `b`: two fall between `a` and `b` [Prop. 8.8]
  have h8 := Elements.Book8.proposition_8 (by omega) (by omega) h19 h17.symm
  -- and `a` is cube, so `b` is cube [Prop. 8.23]
  obtain ⟨-, -, x, y, hx, hy, hxy₁, hxy₂⟩ := h8.two
  exact Elements.Book8.proposition_23 hx hy hb hxy₁ hxy₂ ha'

end Elements.Book9
