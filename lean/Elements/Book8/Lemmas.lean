import Elements.Book8.Definitions

/-
What Book 8 does again and again with any multitude of numbers: ex aequali along a
sequence (Prop. 7.14, one step at a time), and the least numbers in given ratios being
equal to one another. Euclid's "similarly" is induction on the multitude.
-/

namespace Elements.Book8

open Elements.Book7

/-- Numbers the same ratio as themselves, the first to the first and the second to the
second, both being once themselves (Def. 7.20). -/
theorem proportion_self (a b : ℕ) : a ∶ a ∷ b ∶ b :=
  proportion_iff.mpr ⟨1, 1, a, b, Nat.one_pos, Nat.one_pos, (Nat.mul_one a).symm,
    (Nat.mul_one a).symm, (Nat.mul_one b).symm, (Nat.mul_one b).symm⟩

/-- Numbers in the same ratios are, via equality, the first to each as the first to each
[Prop. 7.14]: `b 0 ∶ b i ∷ a 0 ∶ a i`, by 7.14 for three numbers, once for each. -/
theorem SameRatios.extremes {n : ℕ} {a b : Fin (n + 1) → ℕ} (ha : ∀ i, 0 < a i)
    (hb : ∀ i, 0 < b i) (h : SameRatios b a) (i : Fin (n + 1)) :
    b 0 ∶ b i ∷ a 0 ∶ a i := by
  induction i using Fin.induction with
  | zero => exact proportion_self (b 0) (a 0)
  | succ i ih =>
    exact Elements.Book7.proposition_14' (hb 0) (hb _) (hb _) (ha 0) (ha _) (ha _) ih
      (h i)

/-- Alternately [Prop. 7.13]: the first of `b` is to the first of `a` as each of `b` to
each of `a`. -/
theorem SameRatios.alt {n : ℕ} {a b : Fin (n + 1) → ℕ} (ha : ∀ i, 0 < a i)
    (hb : ∀ i, 0 < b i) (h : SameRatios b a) (i : Fin (n + 1)) :
    b 0 ∶ a 0 ∷ b i ∶ a i :=
  Elements.Book7.proposition_13 (hb 0) (hb i) (ha 0) (ha i) (h.extremes ha hb i)

/-- Numbers continuously proportional in the same ratio have the same ratios
[Prop. 5.11]. -/
theorem ContinuedIn.sameRatios {n r s : ℕ} {a b : Fin (n + 1) → ℕ} (hr : 0 < r)
    (hs : 0 < s) (hb : ∀ i, 0 < b i) (ha : ContinuedIn a r s) (hb' : ContinuedIn b r s) :
    SameRatios b a :=
  fun i => proportion_trans (hb _) (hb _) hr hs (hb' i) (ha i).symm

/-- Numbers continuously proportional in the ratio of `r` to `s` are continuously
proportional: each to the next as the first to the second [Prop. 5.11]. -/
theorem ContinuedIn.continued {n r s : ℕ} {a : Fin (n + 1) → ℕ} (ha : ∀ i, 0 < a i)
    (hr : 0 < r) (hs : 0 < s) (h : ContinuedIn a r s) : Continued a := by
  intro i
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.isLt; omega⟩
  have h0 : a 0 ∶ a 1 ∷ r ∶ s := h 0
  exact proportion_trans (ha _) (ha _) hr hs (h i) h0.symm

/-- Continuously proportional numbers are so in the ratio of the first to the second. -/
theorem Continued.continuedIn {n : ℕ} {a : Fin (n + 1) → ℕ} (h : Continued a) :
    ContinuedIn a (a 0) (a 1) := h

/--
The least numbers having the same ratios are one: if `a` and `b` are both least, in the
same ratios, they are equal, each to each. Euclid takes it for granted (8.3: "and they are
equal in multitude, so each is equal to each"). Alternately, as `b 0` is to `a 0`, so is
each of `b` to each of `a`: if `b 0` were less than `a 0`, each of `b` would be less than
each of `a` [Prop. 5.13], and `a` would not be the least; and the same the other way
round. So `b 0` is `a 0`, and the rest are equal [Prop. 5.9]. -- Missed by Euclid.
-/
theorem LeastSeq.eq {n : ℕ} {a b : Fin (n + 1) → ℕ} (ha : ∀ i, 0 < a i)
    (hb : ∀ i, 0 < b i) (hla : LeastSeq a) (hlb : LeastSeq b) (h : SameRatios b a) :
    b = a := by
  have halt := h.alt ha hb
  have h' : SameRatios a b := fun i => (h i).symm
  have hlt : ¬ b 0 < a 0 := fun hlt =>
    hla b hb h fun i => lt_of_proportion (ha 0) (hb 0) (ha i) (halt i).inv hlt
  have hgt : ¬ a 0 < b 0 := fun hgt =>
    hlb a ha h' fun i => lt_of_proportion (hb 0) (ha 0) (hb i) (halt i) hgt
  have h0 : b 0 = a 0 := by omega
  funext i
  have := Elements.Book7.proposition_13 (hb 0) (ha 0) (hb i) (ha i) (halt i)
  rw [h0] at this
  exact (eq_of_proportion (ha 0) (hb i) this)

end Elements.Book8
