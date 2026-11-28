import Elements.Book9.Prop02

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/-- If a cube number multiplies itself, the number made is cube. -/
theorem proposition_3 {a : ℕ} (ha : CubeNumber a) : CubeNumber (a * a) := by
  obtain ⟨c, hc, rfl⟩ := ha
  have hc0 : 0 < c := by omega
  have hd : 0 < c * c := Nat.mul_pos hc0 hc0
  have ha0 : 0 < c * c * c := Nat.mul_pos hd hc0
  have hB : 1 < c * c * c * (c * c * c) := by
    have := one_lt_cube hc
    have := Nat.mul_le_mul this this
    omega
  -- as the unit is to `c`, so `c` is to `d = c * c`, and `d` to `a = d * c` [Def. 7.20]:
  -- two numbers fall between the unit and `a`
  have h₁ := unit_proportion c hc0
  have h₂ := unit_proportion (c * c) hc0
  have hfall := fallBetween_two Nat.one_pos hc0 hd ha0 h₁
    (proportion_trans hc0 hd Nat.one_pos hc0 h₁.symm h₂)
  -- as the unit is to `a`, so `a` is to `b = a * a`: two fall between `a` and `b`
  -- [Prop. 8.8]
  have h8 := Elements.Book8.proposition_8 ha0 (by omega) hfall (unit_proportion _ ha0)
  -- and `a` is cube, so `b` is cube [Prop. 8.23]
  obtain ⟨-, -, x, y, hx, hy, hxy₁, hxy₂⟩ := h8.two
  exact Elements.Book8.proposition_23 hx hy hB hxy₁ hxy₂ ⟨c, hc, rfl⟩

end Elements.Book9
