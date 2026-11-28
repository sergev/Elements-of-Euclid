import Elements.Book8.Prop23

namespace Elements.Book8

open Elements.Book7

/-- If two numbers `a`, `b` have to one another the ratio which a square number `c * c`
has to a square number `d * d`, and the first is square, the second is also square. -/
theorem proposition_24 {a b c d : ℕ} (hc : 0 < c) (hd : 0 < d) (hb : 1 < b)
    (h : a ∶ b ∷ c * c ∶ d * d) (ha : SquareNumber a) : SquareNumber b := by
  obtain ⟨p, hp, hpa⟩ := ha
  have ha : 0 < a := by rw [hpa]; exact Nat.mul_pos (by omega) (by omega)
  -- `c * c`, `d * d` are similar plane numbers, so one number falls between them in mean
  -- proportion [Prop. 8.18]
  have h18 := (proposition_18 hc hc hd hd (proportion_self c d)).1
  -- and as `c * c` is to `d * d`, so `a` to `b`: so one number falls between `a` and `b`
  -- [Prop. 8.8]
  obtain ⟨-, -, e, he, hae⟩ := (proposition_8 ha (by omega) h18 h.symm).one
  -- and `a` is square, so `b` is square [Prop. 8.22]
  exact proposition_22 he hb hae ⟨p, hp, hpa⟩

end Elements.Book8
