import Elements.Book9.Prop07

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/-- From a unit, the fourth is the number after the unit made into a cube: `a 1`
multiplying itself makes `a 2`, and multiplying `a 2` makes `a 3` [Def. 7.20]. -/
theorem unit_three {n : ℕ} {a : Fin (n + 1) → ℕ} (hcon : Continued a) (h0 : a 0 = 1)
    (hn : 3 ≤ n) : a ⟨3, by omega⟩ = a 1 * a 1 * a 1 := by
  rw [unit_succ hcon h0 (k := 2) hn, unit_two hcon h0 (by omega)]

/-- From a unit, the third from the unit and every second after it are square: `a (2 * k)`
for `0 < k`, the unit being `a 0`. The number after the unit is a number. -/
theorem squares_from_unit {n : ℕ} {a : Fin (n + 1) → ℕ} (hcon : Continued a)
    (h0 : a 0 = 1) (h1 : 1 < a 1) :
    ∀ k (hk : 2 * k ≤ n), 0 < k → SquareNumber (a ⟨2 * k, by omega⟩) := by
  have ha := unit_pos hcon h0 h1
  intro k hk hk0
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk'
    · -- the unit measures `a 1` as `a 1` measures `a 2`: `a 1` multiplying itself makes
      -- `a 2`, square [Defs. 7.15, 7.20]
      exact ⟨a 1, h1, unit_two hcon h0 (by omega)⟩
    · -- `a (2 * k)`, `a (2 * k + 1)`, `a (2 * k + 2)` are continuously proportional, and
      -- the first is square, so the third is [Prop. 8.22]
      have h := continued_ratio ha hcon (i := 2 * k) (i' := 2 * k + 1) (j := 2 * k + 1)
        (j' := 2 * (k + 1)) (by omega) (by omega) (by omega) (by omega) hk
      exact Elements.Book8.proposition_22 (ha _) (unit_one_lt hcon h0 h1 hk (by omega)) h
        (ih (by omega) hk')

/-- From a unit, the fourth from the unit and every third after it are cube: `a (3 * k)`
for `0 < k`. -/
theorem cubes_from_unit {n : ℕ} {a : Fin (n + 1) → ℕ} (hcon : Continued a)
    (h0 : a 0 = 1) (h1 : 1 < a 1) :
    ∀ k (hk : 3 * k ≤ n), 0 < k → CubeNumber (a ⟨3 * k, by omega⟩) := by
  have ha := unit_pos hcon h0 h1
  intro k hk hk0
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk'
    · -- the unit measures `a 1` as `a 2` measures `a 3`: `a 1` multiplying `a 2` makes
      -- `a 3`, and `a 2` is `a 1` multiplying itself, so `a 3` is cube [Def. 7.19]
      exact ⟨a 1, h1, unit_three hcon h0 (by omega)⟩
    · -- `a (3 * k)`, …, `a (3 * k + 3)` are continuously proportional, and the first is
      -- cube, so the fourth is [Prop. 8.23]
      have h₁ := continued_ratio ha hcon (i := 3 * k) (i' := 3 * k + 1) (j := 3 * k + 1)
        (j' := 3 * k + 2) (by omega) (by omega) (by omega) (by omega) (by omega)
      have h₂ := continued_ratio ha hcon (i := 3 * k + 1) (i' := 3 * k + 2)
        (j := 3 * k + 2) (j' := 3 * (k + 1)) (by omega) (by omega) (by omega) (by omega)
        hk
      exact Elements.Book8.proposition_23 (ha _) (ha _)
        (unit_one_lt hcon h0 h1 hk (by omega)) h₁ h₂ (ih (by omega) hk')

/--
If any multitude of numbers `a 0`, …, `a n` are continuously proportional from a unit,
the third from the unit is square, and every second after it, `a (2 * k)`; the fourth is
cube, and every third after it, `a (3 * k)`; and the seventh is both, and every sixth
after it, `a (6 * k)`. The unit is the first, `a 0`; the number after it is a number.
Euclid shows the first of each and says "similarly": the proof is by induction on `k`.
-/
theorem proposition_8 {n : ℕ} {a : Fin (n + 1) → ℕ} (hcon : Continued a) (h0 : a 0 = 1)
    (h1 : 1 < a 1) :
    (∀ k (hk : 2 * k ≤ n), 0 < k → SquareNumber (a ⟨2 * k, by omega⟩)) ∧
    (∀ k (hk : 3 * k ≤ n), 0 < k → CubeNumber (a ⟨3 * k, by omega⟩)) ∧
    (∀ k (hk : 6 * k ≤ n), 0 < k →
      SquareNumber (a ⟨6 * k, by omega⟩) ∧ CubeNumber (a ⟨6 * k, by omega⟩)) := by
  refine ⟨squares_from_unit hcon h0 h1, cubes_from_unit hcon h0 h1, fun k hk hk0 => ?_⟩
  -- it was shown to be square, and cube
  have hs := squares_from_unit hcon h0 h1 (3 * k) (by omega) (by omega)
  have hc := cubes_from_unit hcon h0 h1 (2 * k) (by omega) (by omega)
  have e₁ : (⟨2 * (3 * k), by omega⟩ : Fin (n + 1)) = ⟨6 * k, by omega⟩ :=
    Fin.ext (by simp only; omega)
  have e₂ : (⟨3 * (2 * k), by omega⟩ : Fin (n + 1)) = ⟨6 * k, by omega⟩ :=
    Fin.ext (by simp only; omega)
  rw [e₁] at hs
  rw [e₂] at hc
  exact ⟨hs, hc⟩

end Elements.Book9
