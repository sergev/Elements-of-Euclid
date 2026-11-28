import Elements.Book8.Prop24

namespace Elements.Book8

open Elements.Book7

/-- If two numbers `a`, `b` have to one another the ratio which a cube number
`c * c * c` has to a cube number `d * d * d`, and the first is cube, the second is also
cube. -/
theorem proposition_25 {a b c d : ℕ} (hc : 0 < c) (hd : 0 < d) (hb : 1 < b)
    (h : a ∶ b ∷ c * c * c ∶ d * d * d) (ha : CubeNumber a) : CubeNumber b := by
  obtain ⟨p, hp, hpa⟩ := ha
  have ha : 0 < a := by
    rw [hpa]; exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  -- `c * c * c`, `d * d * d` are similar solid numbers, so two numbers fall between them
  -- in mean proportion [Prop. 8.19]
  have h19 := (proposition_19 hc hc hc hd hd hd (proportion_self c d)
    (proportion_self c d)).1
  -- and as many fall between `a` and `b`, in the same ratio [Prop. 8.8]: `e` and `f`
  obtain ⟨-, -, e, f, he, hf, h₁, h₂⟩ := (proposition_8 ha (by omega) h19 h.symm).two
  -- `a`, `e`, `f`, `b` are continuously proportional, and `a` is cube, so `b` is cube
  -- [Prop. 8.23]
  exact proposition_23 he hf hb h₁ h₂ ⟨p, hp, hpa⟩

end Elements.Book8
