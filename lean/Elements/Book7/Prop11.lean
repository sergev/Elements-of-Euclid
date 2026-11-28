import Elements.Book7.Prop10

namespace Elements.Book7

/-- If as the whole `a` is to the whole `b`, so `e` taken away is to `f` taken away, then
the remainder `a - e` is to the remainder `b - f` as the whole to the whole. -/
theorem proposition_11 {a b e f : ℕ} (hea : e ≤ a) (hfb : f ≤ b) (h : a ∶ b ∷ e ∶ f) :
    a - e ∶ b - f ∷ a ∶ b := by
  -- whichever part, or parts, `a` is of `b`, `e` is the same of `f` [Def. 7.20]; so is
  -- the remainder of the remainder [Props. 7.7, 7.8]
  rcases h with ⟨n, hn, h₁, h₂⟩ | ⟨n, h₁, h₂⟩ | ⟨m, n, h₁, h₂⟩ | ⟨m, n, h₁, h₂⟩
  · rcases Nat.lt_or_ge 1 n with hn1 | hn1
    · exact Or.inl ⟨n, hn, (proposition_7 ⟨hn1, h₁⟩ ⟨hn1, h₂⟩ hfb).2, h₁⟩
    · obtain rfl : n = 1 := by omega
      rw [Nat.mul_one] at h₁ h₂
      subst h₁ h₂
      exact Or.inl ⟨1, hn, (Nat.mul_one _).symm, (Nat.mul_one _).symm⟩
  · exact Or.inr (Or.inl ⟨n, proposition_7 h₁ h₂ hea, h₁⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨m, n, proposition_8 h₁ h₂ hea, h₁⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨m, n, proposition_8 h₁ h₂ hfb, h₁⟩))

end Elements.Book7
