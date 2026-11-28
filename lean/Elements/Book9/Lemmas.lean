import Elements.Book9.Definitions

/-
What Book 9 takes from Book 7 and does again: Def. 7.7's second reading, the least number
measured by any multitude (7.36, for any multitude), and the sums of 9.35, 9.36.
-/

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/-! Odd and even. -/

/-- Every number, and the unit, is even or odd (Defs. 7.6, 7.7). -/
theorem even_or_odd {a : ℕ} (ha : 0 < a) : EvenNumber a ∨ OddNumber a := by
  by_cases h : EvenNumber a
  · exact Or.inl h
  · exact Or.inr ⟨ha, h⟩

/-- An even number is not odd. -/
theorem EvenNumber.not_odd {a : ℕ} (h : EvenNumber a) : ¬ OddNumber a :=
  fun ho => ho.2 h

/-- An even number is a number, greater than the unit. -/
theorem EvenNumber.one_lt {a : ℕ} (h : EvenNumber a) : 1 < a := by
  obtain ⟨h, hh, rfl⟩ := h
  omega

/-- Def. 7.7, the second reading: an odd number differs from an even number by a unit,
`a = h + h + 1`; for the unit, `h` is nothing. -/
theorem odd_iff {a : ℕ} : OddNumber a ↔ ∃ h, a = h + h + 1 := by
  constructor
  · rintro ⟨ha, hne⟩
    refine ⟨a / 2, ?_⟩
    by_contra hne'
    exact hne ⟨a / 2, by omega, by omega⟩
  · rintro ⟨h, rfl⟩
    exact ⟨by omega, fun ⟨k, _, hk⟩ => by omega⟩

/-- An odd number less a unit is even, or nothing for the unit (Def. 7.7). -/
theorem OddNumber.sub_unit {a : ℕ} (h : OddNumber a) (ha : 1 < a) :
    EvenNumber (a - 1) := by
  obtain ⟨k, rfl⟩ := odd_iff.mp h
  exact ⟨k, by omega, by omega⟩

/-- An even number and a unit make an odd number (Def. 7.7). -/
theorem EvenNumber.add_unit {a : ℕ} (h : EvenNumber a) : OddNumber (a + 1) := by
  obtain ⟨k, -, rfl⟩ := h
  exact odd_iff.mpr ⟨k, rfl⟩

/-! The least number measured by any multitude: Euclid's 7.36, done once more for each
number added. -/

/-- The least number measured by `a 0`, …, `a n` measures every number they all measure,
as 7.35 for two. -/
theorem exists_leastMeasuredSeq' {n : ℕ} {a : Fin (n + 1) → ℕ} (ha : ∀ i, 0 < a i) :
    ∃ c, LeastMeasuredSeq c a ∧ ∀ d, (∀ i, a i ∣ d) → c ∣ d := by
  induction n with
  | zero =>
    refine ⟨a 0, ⟨ha 0, fun i => ?_, fun d _ hd => ?_⟩, fun d hd => ?_⟩
    · rw [Fin.fin_one_eq_zero i]
    · exact le_of_measures (by assumption) (hd 0)
    · exact hd 0
  | succ n ih =>
    -- the least number `c` the first `n + 1` measure, and the least `e` that `c` and the
    -- last measure [Prop. 7.34]
    obtain ⟨c, ⟨hc, hac, -⟩, hcd⟩ := ih (a := fun i => a i.castSucc) fun i => ha _
    obtain ⟨e, he⟩ := Elements.Book7.proposition_34 hc (ha (Fin.last _))
    have hmeas : ∀ d, (∀ i, a i ∣ d) → e ∣ d := fun d hd =>
      -- `c` measures every number they measure, and so does `e` [Prop. 7.35]
      Elements.Book7.proposition_35 he (hcd d fun i => hd _) (hd _)
    refine ⟨e, ⟨he.1, fun i => ?_, fun d hd hdi => le_of_measures hd (hmeas d hdi)⟩,
      hmeas⟩
    induction i using Fin.lastCases with
    | last => exact he.2.2.1
    | cast i => exact measures_trans (hac i) he.2.1

/-- There is a least number measured by any multitude of numbers [Prop. 7.36]. -/
theorem exists_leastMeasuredSeq {n : ℕ} {a : Fin (n + 1) → ℕ} (ha : ∀ i, 0 < a i) :
    ∃ c, LeastMeasuredSeq c a :=
  (exists_leastMeasuredSeq' ha).imp fun _ h => h.1

/-- The least number measured by any multitude measures every number they all measure
[Prop. 7.35]. -/
theorem LeastMeasuredSeq.measures {n c d : ℕ} {a : Fin (n + 1) → ℕ} (ha : ∀ i, 0 < a i)
    (hc : LeastMeasuredSeq c a) (hd : ∀ i, a i ∣ d) : c ∣ d := by
  obtain ⟨c', hc', hm⟩ := exists_leastMeasuredSeq' ha
  have h₁ : c' ∣ c := hm c hc.2.1
  have h₂ : c ≤ c' := hc.2.2 c' hc'.1 hc'.2.1
  have : c' = c := Nat.le_antisymm (le_of_measures hc.1 h₁) h₂
  exact this ▸ hm d hd

/-! Sums (9.35, 9.36). -/

/-- All of `n + 2` numbers are all but the last, and the last (Book 7's `sum`). -/
theorem sum_succ {n : ℕ} (a : Fin (n + 2) → ℕ) :
    sum a = sum (fun i : Fin (n + 1) => a i.castSucc) + a (Fin.last (n + 1)) := rfl

/-- The unit and the numbers doubled from it, up to the last, are a unit less than the
last doubled once more. -/
theorem sum_powers_two (n : ℕ) :
    sum (powers 1 2 n) + 1 = powers 1 2 (n + 1) (Fin.last (n + 1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sum_succ, powers_last, powers_last]
    have : (fun i : Fin (n + 1) => powers 1 2 (n + 1) i.castSucc) = powers 1 2 n := by
      funext i; rw [powers_castSucc, Nat.mul_one]
    rw [this, powers_last] at *
    omega

end Elements.Book9
