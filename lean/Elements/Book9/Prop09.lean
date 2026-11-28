import Elements.Book9.Prop08

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/--
If any multitude of numbers are continuously proportional from a unit, and the number
after the unit is square, all the rest are square; and if it is cube, all the rest are
cube. Euclid takes each from the one two places (three places) before it, by 8.22
(8.23), and says "similarly": the proof is by induction.
-/
theorem proposition_9 {n : ℕ} {a : Fin (n + 1) → ℕ} (hcon : Continued a) (h0 : a 0 = 1) :
    (SquareNumber (a 1) → ∀ k (hk : k ≤ n), 0 < k → SquareNumber (a ⟨k, by omega⟩)) ∧
    (CubeNumber (a 1) → ∀ k (hk : k ≤ n), 0 < k → CubeNumber (a ⟨k, by omega⟩)) := by
  constructor
  · intro hs
    have h1 : 1 < a 1 := by
      obtain ⟨p, hp, hp'⟩ := hs
      have := Nat.mul_le_mul hp hp
      omega
    have ha := unit_pos hcon h0 h1
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk hk0
      match k, ih, hk, hk0 with
      | 1, _, hk, _ => rw [fin_one_eq hk]; exact hs
      | 2, _, hk, _ =>
        -- the third from the unit is square [Prop. 9.8]
        exact (proposition_8 hcon h0 h1).1 1 hk Nat.one_pos
      | k + 3, ih, hk, _ =>
        -- `a (k + 1)`, `a (k + 2)`, `a (k + 3)` are continuously proportional, and the
        -- first is square, so the third is square [Prop. 8.22]
        have h := continued_ratio ha hcon (i := k + 1) (i' := k + 2) (j := k + 2)
          (j' := k + 3) (by omega) (by omega) (by omega) (by omega) hk
        exact Elements.Book8.proposition_22 (ha _) (unit_one_lt hcon h0 h1 hk (by omega))
          h (ih (k + 1) (by omega) (by omega) (by omega))
  · intro hc
    have h1 : 1 < a 1 := by
      obtain ⟨p, hp, hp'⟩ := hc
      have := one_lt_cube hp
      omega
    have ha := unit_pos hcon h0 h1
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk hk0
      match k, ih, hk, hk0 with
      | 1, _, hk, _ => rw [fin_one_eq hk]; exact hc
      | 2, _, hk, _ =>
        -- `a 1` multiplying itself makes `a 2`, so it is cube [Prop. 9.3]
        rw [unit_two hcon h0 hk]
        exact proposition_3 hc
      | 3, _, hk, _ =>
        -- the fourth from the unit is cube [Prop. 9.8]
        exact (proposition_8 hcon h0 h1).2.1 1 hk Nat.one_pos
      | k + 4, ih, hk, _ =>
        -- `a (k + 1)`, …, `a (k + 4)` are continuously proportional, and the first is
        -- cube, so the fourth is cube [Prop. 8.23]
        have h₁ := continued_ratio ha hcon (i := k + 1) (i' := k + 2) (j := k + 2)
          (j' := k + 3) (by omega) (by omega) (by omega) (by omega) (by omega)
        have h₂ := continued_ratio ha hcon (i := k + 2) (i' := k + 3) (j := k + 3)
          (j' := k + 4) (by omega) (by omega) (by omega) (by omega) hk
        exact Elements.Book8.proposition_23 (ha _) (ha _)
          (unit_one_lt hcon h0 h1 hk (by omega)) h₁ h₂
          (ih (k + 1) (by omega) (by omega) (by omega))

end Elements.Book9
