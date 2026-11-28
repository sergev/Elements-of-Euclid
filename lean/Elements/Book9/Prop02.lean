import Elements.Book9.Prop01

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/--
If two numbers `a`, `b` multiplying one another make a square, they are similar plane
numbers: `p * q` and `r * s` with `p ∶ q ∷ r ∶ s`. As in 8.20, the sides may be the unit
(`2 * 8` is square, and `2` is prime), so they are stated positive.
-/
theorem proposition_2 {a b x : ℕ} (ha : 0 < a) (hb : 0 < b) (hx : 0 < x)
    (h : b * a = x * x) :
    ∃ p q r s, 0 < p ∧ 0 < q ∧ 0 < r ∧ 0 < s ∧ a = p * q ∧ b = r * s ∧ p ∶ q ∷ r ∶ s := by
  -- let `a` multiplying itself make `d`: as `a` is to `b`, so `d` is to `c` [Prop. 7.17]
  have h17 := Elements.Book7.proposition_17 ha ha hb
  rw [h] at h17
  -- `d` and `c` are squares, so similar plane numbers, and one number falls between
  -- them [Prop. 8.18]
  have h18 := (Elements.Book8.proposition_18 ha ha hx hx (proportion_self a x)).1
  -- and as `d` is to `c`, so `a` is to `b`: one falls between `a` and `b` [Prop. 8.8]
  have h8 := Elements.Book8.proposition_8 ha hb h18 h17.symm
  -- so they are similar plane numbers [Prop. 8.20]
  exact Elements.Book8.proposition_20 h8

end Elements.Book9
