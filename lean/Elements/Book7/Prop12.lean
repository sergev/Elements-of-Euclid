import Elements.Book7.Prop11

namespace Elements.Book7

/-- Euclid's case, two pairs: if `a ∶ b ∷ c ∶ d`, then `a ∶ b ∷ a + c ∶ b + d`. -/
theorem proposition_12' {a b c d : ℕ} (h : a ∶ b ∷ c ∶ d) : a ∶ b ∷ a + c ∶ b + d := by
  -- whichever part, or parts, `a` is of `b`, `c` is the same of `d` [Def. 7.20]; so is
  -- the sum of the sum [Props. 7.5, 7.6]
  rcases h with ⟨n, hn, h₁, h₂⟩ | ⟨n, h₁, h₂⟩ | ⟨m, n, h₁, h₂⟩ | ⟨m, n, h₁, h₂⟩
  · exact Or.inl ⟨n, hn, h₁, by rw [h₁, h₂, proposition_5']⟩
  · exact Or.inr (Or.inl ⟨n, h₁, proposition_5 h₁ h₂⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨m, n, h₁, proposition_6 h₁ h₂⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨m, n, h₁, proposition_6 h₁ h₂⟩))

/--
If any multitude of numbers are proportional, `a i ∶ b i ∷ a 0 ∶ b 0`, then as one of the
leading is to one of the following, so all of the leading are to all of the following.
-/
theorem proposition_12 {n : ℕ} {a b : Fin (n + 1) → ℕ} (ha : ∀ i, 0 < a i)
    (hb : ∀ i, 0 < b i) (h : ∀ i, a i ∶ b i ∷ a 0 ∶ b 0) : a 0 ∶ b 0 ∷ sum a ∶ sum b := by
  induction n with
  | zero => exact Proportion.refl (ha 0) (hb 0)
  | succ n ih =>
    -- the leading and the following but the last
    have ih := ih (a := fun i => a i.castSucc) (b := fun i => b i.castSucc)
      (fun i => ha _) (fun i => hb _) (fun i => h _)
    have hsa := sum_pos (a := fun i : Fin (n + 1) => a i.castSucc) fun i => ha _
    have hsb := sum_pos (a := fun i : Fin (n + 1) => b i.castSucc) fun i => hb _
    -- the last is to its following as they are -- Missed by Euclid.
    have hl := proportion_trans hsa hsb (ha 0) (hb 0) ih.symm (h (Fin.last (n + 1))).symm
    -- and all of them [Prop. 7.12, two pairs]
    exact proportion_trans (ha 0) (hb 0) hsa hsb ih (proposition_12' hl)

end Elements.Book7
