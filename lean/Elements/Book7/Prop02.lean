import Elements.Book7.Prop01

namespace Elements.Book7

/-- Euclid's argument: the last remainder measures the number before it, so each number
before, being the remainder and the numbers it measures, and so `a` and `b`. -/
theorem remainder_measures (a b : ℕ) : remainder a b ∣ a ∧ remainder a b ∣ b := by
  fun_induction remainder a b with
  | case1 b => exact ⟨⟨0, rfl⟩, measures_self b⟩
  | case2 a => exact ⟨measures_self a, ⟨0, rfl⟩⟩
  -- it measures `a` and the remainder `b - a`, so the whole `b`
  | case3 a b _ _ h ih =>
    refine ⟨ih.1, ?_⟩
    have := measures_add ih.2 ih.1
    rwa [Nat.sub_add_cancel h.le] at this
  | case4 a b _ _ _ h ih =>
    refine ⟨?_, ih.2⟩
    have := measures_add ih.1 ih.2
    rwa [Nat.sub_add_cancel h.le] at this
  | case5 a b _ _ _ _ => exact ⟨measures_self a, by rw [show b = a by omega]⟩

/--
To find the greatest common measure of two numbers `a`, `b` not prime to one another.
It is `b` if `b` measures `a`, and otherwise the remainder of the process of 7.1.
-/
theorem proposition_2 {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h : ¬ PrimeTo a b) :
    ∃ g, 1 < g ∧ GreatestCommonMeasure g a b := by
  by_cases hba : b ∣ a
  · -- `b` measures `a`, and itself; nothing greater than `b` measures `b`
    refine ⟨b, ?_, hba, measures_self b, fun e _ heb => le_of_measures hb heb⟩
    by_contra hb1
    obtain rfl : b = 1 := by omega
    exact h fun e _ he => Nat.eq_one_of_dvd_one he
  · -- a unit will not be left, or `a`, `b` are prime to one another [Prop. 7.1]
    have h1 : remainder a b ≠ 1 := fun h1 => h (proposition_1 h1)
    have hpos := remainder_pos ha hb
    -- the remainder measures `a` and `b`
    obtain ⟨hra, hrb⟩ := remainder_measures a b
    refine ⟨remainder a b, by omega, hra, hrb, fun e hea heb => ?_⟩
    -- a greater number measuring `a` and `b` measures the remainder: impossible
    by_contra hlt
    exact not_measures_of_lt hpos (by omega) (measures_remainder hea heb)

/-- The greatest common measure is the remainder of the process. -/
theorem remainder_of_greatest {g a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hg : GreatestCommonMeasure g a b) : g = remainder a b := by
  obtain ⟨hga, hgb, hgreat⟩ := hg
  obtain ⟨hra, hrb⟩ := remainder_measures a b
  exact Nat.le_antisymm
    (le_of_measures (remainder_pos ha hb) (measures_remainder hga hgb)) (hgreat _ hra hrb)

/-- If a number measures two numbers, it measures their greatest common measure. -/
theorem proposition_2_corollary {e g a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hg : GreatestCommonMeasure g a b) (hea : e ∣ a) (heb : e ∣ b) : e ∣ g := by
  rw [remainder_of_greatest ha hb hg]
  exact measures_remainder hea heb

end Elements.Book7
