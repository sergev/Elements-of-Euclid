import Elements.Book9.Lemmas

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/--
If two similar plane numbers multiply one another, the number made is square. The similar
plane numbers are taken as Book 8 takes them (8.18): `c * d` and `e * f` with
`c ∶ d ∷ e ∶ f`; the first is a number, greater than the unit.
-/
theorem proposition_1 {c d e f : ℕ} (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (hA : 1 < c * d) (h : c ∶ d ∷ e ∶ f) : SquareNumber (e * f * (c * d)) := by
  have hB : 0 < e * f := Nat.mul_pos he hf
  have hC : 1 < e * f * (c * d) := by
    have := Nat.mul_le_mul_right (c * d) hB
    omega
  -- let `a` multiplying itself make `d'`: as `a` is to `b`, so `d'` is to `c'`
  -- [Prop. 7.17]
  have h17 := Elements.Book7.proposition_17 (a := c * d) (b := c * d) (by omega)
    (by omega) hB
  -- one number falls between `a` and `b` [Prop. 8.18], so between `d'` and `c'`
  -- [Prop. 8.8]
  have h8 := Elements.Book8.proposition_8 (Nat.mul_pos (by omega) (by omega)) (by omega)
    (Elements.Book8.proposition_18 hc hd he hf h).1 h17
  obtain ⟨-, -, x, hx, hmean⟩ := h8.one
  -- and `d'` is square, so `c'` is square [Prop. 8.22]
  exact Elements.Book8.proposition_22 hx hC hmean ⟨c * d, hA, rfl⟩

end Elements.Book9
