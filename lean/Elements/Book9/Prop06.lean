import Elements.Book9.Prop05

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/--
If a number `a` multiplying itself makes a cube number, it is itself cube. `a` is a
number, greater than the unit. Euclid concludes by 8.23 from the cube `b` back to `a`,
the four numbers taken the other way round.
-/
theorem proposition_6 {a : ℕ} (ha : 1 < a) (hb : CubeNumber (a * a)) : CubeNumber a := by
  have ha0 : 0 < a := by omega
  have hb0 : 0 < a * a := Nat.mul_pos ha0 ha0
  have hc0 : 0 < a * a * a := Nat.mul_pos hb0 ha0
  obtain ⟨q, hq, hbq⟩ := hb
  -- let `a` multiplying `b` make `c`, cube [Def. 7.19]
  -- as the unit is to `a`, so `a` is to `b`, and so `b` is to `c` [Def. 7.20]; so as `a`
  -- is to `b`, so `b` is to `c`
  have h₁ := unit_proportion a ha0
  have h₂ := unit_proportion (a * a) ha0
  have hab := proportion_trans ha0 hb0 Nat.one_pos ha0 h₁.symm h₂
  -- `b` and `c` are cube, so similar solid numbers: two numbers fall between them
  -- [Prop. 8.19]
  have h19 := fallBetween_cubes (show 0 < q by omega) ha0
  rw [← hbq] at h19
  -- as `b` is to `c`, so `a` is to `b`: two fall between `a` and `b` [Prop. 8.8]
  have h8 := Elements.Book8.proposition_8 ha0 hb0 h19 hab.symm
  obtain ⟨-, -, x, y, hx, hy, hxy₁, hxy₂⟩ := h8.two
  -- and `b` is cube, so `a` is cube [Prop. 8.23], taking them from `b` back to `a`
  exact Elements.Book8.proposition_23 hy hx ha hxy₂.inv.symm hxy₁.inv.symm
    ⟨q, hq, hbq⟩

end Elements.Book9
