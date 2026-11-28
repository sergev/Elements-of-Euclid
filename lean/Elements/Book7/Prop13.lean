import Elements.Book7.Prop12

namespace Elements.Book7

/-- If four numbers are proportional, `a ∶ b ∷ c ∶ d`, then they are also proportional
alternately, `a ∶ c ∷ b ∶ d`. Stated for the unit as well. -/
theorem proposition_13 {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a ∶ b ∷ c ∶ d) : a ∶ c ∷ b ∶ d := by
  -- whichever part, or parts, `a` is of `b`, `c` is the same of `d` [Def. 7.20]; so,
  -- alternately, whichever `a` is of `c`, `b` is the same of `d` [Props. 7.9, 7.10]
  rcases h with ⟨n, hn, h₁, h₂⟩ | ⟨n, h₁, h₂⟩ | ⟨m, n, h₁, h₂⟩ | ⟨m, n, h₁, h₂⟩
  · rcases Nat.lt_or_ge 1 n with hn1 | hn1
    · exact (proposition_9 hb hd ⟨hn1, h₁⟩ ⟨hn1, h₂⟩).symm
    · obtain rfl : n = 1 := by omega
      rw [Nat.mul_one] at h₁ h₂
      subst h₁ h₂
      exact Proportion.refl ha hc
  · exact proposition_9 ha hc h₁ h₂
  · exact proposition_10 ha hc h₁ h₂
  · exact (proposition_10 hb hd h₁ h₂).symm

end Elements.Book7
