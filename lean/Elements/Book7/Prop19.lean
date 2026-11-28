import Elements.Book7.Prop18

namespace Elements.Book7

/--
Four numbers are proportional, `a ∶ b ∷ c ∶ d`, exactly when the number made by the first
and the fourth, `d * a`, is equal to the number made by the second and the third, `c * b`.
-/
theorem proposition_19 {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    a ∶ b ∷ c ∶ d ↔ d * a = c * b := by
  -- let `a` multiplying `c` make `g`: as `c` is to `d`, so is `g` to `d * a` [Prop. 7.17]
  have h₁ := proposition_17 ha hc hd
  -- and `a`, `b` multiplying `c` make `g` and `c * b`: as `a` to `b`, so is `g` to
  -- `c * b` [Prop. 7.18]
  have h₂ := proposition_18 ha hb hc
  have hg := Nat.mul_pos hc ha
  constructor
  · intro h
    -- as `a` is to `b`, so is `g` to `d * a` -- Missed by Euclid.
    have h₃ := proportion_trans ha hb hc hd h h₁
    -- so `g` has the same ratio to each of `d * a` and `c * b` -- Missed by Euclid.
    have h₄ := proportion_trans hg (Nat.mul_pos hd ha) ha hb h₃.symm h₂
    -- they are equal [Prop. 5.9]
    exact eq_of_proportion hg (Nat.mul_pos hd ha) h₄
  · intro h
    -- `g` is to `d * a` as to `c * b` [Prop. 5.7]
    have h₃ := proportion_of_eq hg (Nat.mul_pos hd ha) h
    -- and as `a` to `b`, and as `c` to `d` -- Missed by Euclid.
    have h₄ := proportion_trans hg (Nat.mul_pos hd ha) hg (Nat.mul_pos hc hb) h₃ h₂.symm
    exact proportion_trans ha hb hg (Nat.mul_pos hd ha) h₄.symm h₁.symm

end Elements.Book7
