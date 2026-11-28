import Elements.Book9.Prop03

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/-- Similar solid numbers: two numbers fall between cube numbers [Prop. 8.19]. -/
theorem fallBetween_cubes {c d : ℕ} (hc : 0 < c) (hd : 0 < d) :
    FallBetween 2 (c * c * c) (d * d * d) :=
  (Elements.Book8.proposition_19 hc hc hc hd hd hd (proportion_self c d)
    (proportion_self c d)).1

/-- If a cube number `a` multiplies another cube number `b`, the number made is cube. -/
theorem proposition_4 {a b : ℕ} (ha : CubeNumber a) (hb : CubeNumber b) :
    CubeNumber (b * a) := by
  have hd := proposition_3 ha
  obtain ⟨p, hp, rfl⟩ := ha
  obtain ⟨q, hq, rfl⟩ := hb
  have ha0 := one_lt_cube hp
  have hb0 := one_lt_cube hq
  -- let `a` multiplying itself make `d`, cube [Prop. 9.3]; as `a` is to `b`, so `d` is to
  -- `c` [Prop. 7.17]
  have h17 := Elements.Book7.proposition_17 (by omega) (by omega) (by omega)
    (a := p * p * p) (b := p * p * p) (c := q * q * q)
  -- `a`, `b` are similar solid numbers: two numbers fall between them [Prop. 8.19], and
  -- so between `d` and `c` [Prop. 8.8]
  have h8 := Elements.Book8.proposition_8 (Nat.mul_pos (by omega) (by omega))
    (Nat.mul_pos (by omega) (by omega)) (fallBetween_cubes (by omega) (by omega)) h17
  -- and `d` is cube, so `c` is cube [Prop. 8.23]
  obtain ⟨-, -, x, y, hx, hy, hxy₁, hxy₂⟩ := h8.two
  have hC : 1 < q * q * q * (p * p * p) := by
    have := Nat.mul_le_mul_right (p * p * p) (show 1 ≤ q * q * q by omega)
    omega
  exact Elements.Book8.proposition_23 hx hy hC hxy₁ hxy₂ hd

end Elements.Book9
