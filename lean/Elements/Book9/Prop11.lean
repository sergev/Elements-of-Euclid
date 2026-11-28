import Elements.Book9.Prop10

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/-- Euclid's argument in 9.11: as the unit is to `a i`, so `a (j - i)` is to `a j`
[Prop. 9.8's step, via equality]; so the unit measures `a (j - i)` as many times as `a i`
measures `a j` [Prop. 7.15], and `a i` measures `a j` according to `a (j - i)`. -/
theorem measures_from_unit {n : ℕ} {a : Fin (n + 1) → ℕ} (hcon : Continued a)
    (h0 : a 0 = 1) (h1 : 1 < a 1) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    a ⟨j, by omega⟩ = a ⟨i, by omega⟩ * a ⟨j - i, by omega⟩ := by
  have ha := unit_pos hcon h0 h1
  -- as the unit is to `a i`, so `a (j - i)` is to `a j`
  have h := continued_ratio ha hcon (i := 0) (i' := i) (j := j - i) (j' := j)
    (by omega) (by omega) (by omega) (by omega) hj
  rw [show (⟨0, by omega⟩ : Fin (n + 1)) = 0 from rfl, h0] at h
  -- the unit measures `a i` according to its units, and `a (j - i)` measures `a j` as
  -- many times [Def. 7.20]
  have he := eq_mul_of_unit h
  -- alternately, the unit measures `a (j - i)` as many times as `a i` measures `a j`
  -- [Prop. 7.15]
  obtain ⟨m, hm, hjm⟩ := Elements.Book7.proposition_15 (ha _) (ha _)
    (Nat.one_mul _).symm he
  rw [Nat.one_mul] at hm
  rw [hjm, hm]

/-- If any multitude of numbers are continuously proportional from a unit, a lesser
measures a greater according to one of the proportional numbers. -/
theorem proposition_11 {n : ℕ} {a : Fin (n + 1) → ℕ} (hcon : Continued a) (h0 : a 0 = 1)
    (h1 : 1 < a 1) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    ∃ k : Fin (n + 1), a ⟨j, by omega⟩ = a ⟨i, by omega⟩ * a k :=
  ⟨_, measures_from_unit hcon h0 h1 hij hj⟩

/-- Corollary: the number according to which it measures is as far from the measured as
the measuring is from the unit: `a i` measures `a j` according to `a (j - i)`. -/
theorem proposition_11_corollary {n : ℕ} {a : Fin (n + 1) → ℕ} (hcon : Continued a)
    (h0 : a 0 = 1) (h1 : 1 < a 1) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    a ⟨j, by omega⟩ = a ⟨i, by omega⟩ * a ⟨j - i, by omega⟩ :=
  measures_from_unit hcon h0 h1 hij hj

end Elements.Book9
