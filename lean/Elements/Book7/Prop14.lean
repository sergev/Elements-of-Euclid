import Elements.Book7.Prop13

namespace Elements.Book7

/-- Euclid's case, three numbers: if `a ∶ b ∷ d ∶ e` and `b ∶ c ∷ e ∶ f`, then, via
equality, `a ∶ c ∷ d ∶ f`. -/
theorem proposition_14' {a b c d e f : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f) (h₁ : a ∶ b ∷ d ∶ e) (h₂ : b ∶ c ∷ e ∶ f) :
    a ∶ c ∷ d ∶ f := by
  -- alternately, `a ∶ d ∷ b ∶ e` and `b ∶ e ∷ c ∶ f` [Prop. 7.13]
  have h₁' := proposition_13 ha hb hd he h₁
  have h₂' := proposition_13 hb hc he hf h₂
  -- so `a ∶ d ∷ c ∶ f` -- Missed by Euclid.
  have h := proportion_trans ha hd hb he h₁' h₂'
  -- alternately [Prop. 7.13]
  exact proposition_13 ha hd hc hf h

/--
If any multitude of numbers `a 0`, …, `a n` and as many others `d 0`, …, `d n` are in the
same ratio taken two by two, `a i ∶ a (i + 1) ∷ d i ∶ d (i + 1)`, then they are in the
same ratio via equality, `a 0 ∶ a n ∷ d 0 ∶ d n`.
-/
theorem proposition_14 {n : ℕ} {a d : Fin (n + 1) → ℕ} (ha : ∀ i, 0 < a i)
    (hd : ∀ i, 0 < d i)
    (h : ∀ i : Fin n, a i.castSucc ∶ a i.succ ∷ d i.castSucc ∶ d i.succ) :
    a 0 ∶ a (Fin.last n) ∷ d 0 ∶ d (Fin.last n) := by
  induction n with
  | zero => exact Or.inl ⟨1, Nat.one_pos, (Nat.mul_one _).symm, (Nat.mul_one _).symm⟩
  | succ n ih =>
    -- all but the last
    have ih := ih (a := fun i => a i.castSucc) (d := fun i => d i.castSucc)
      (fun i => ha _) (fun i => hd _) (fun i => h i.castSucc)
    -- and the last [Prop. 7.14, three numbers]
    exact proposition_14' (ha _) (ha _) (ha _) (hd _) (hd _) (hd _) ih (h (Fin.last n))

end Elements.Book7
