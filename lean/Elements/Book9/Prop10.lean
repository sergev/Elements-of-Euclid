import Elements.Book9.Prop09

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/--
If any multitude of numbers are continuously proportional from a unit, and the number
after the unit is not square, no other is square but the third from the unit and every
second after it, `a (2 * k)`; and if it is not cube, no other is cube but the fourth from
the unit and every third after it, `a (3 * k)`.

Euclid: if `a 3` were square, `a 2` being square [Prop. 9.8], as `a 2` is to `a 3`, so
`a 1` is to `a 2`, the ratio of a square to a square; so `a 1`, `a 2` are similar plane
numbers [Prop. 8.26], and `a 2` is square, so `a 1` is. Prop. 8.26 is the converse, and
"similar plane, one square" does not give a square (8.22); the step is Prop. 8.24, which
is what is cited here. For cubes he takes `a 4`; a number two places after a cube,
`a (3 * k + 2)`, is "similarly", through `a 1` to `a 3`.
-/
theorem proposition_10 {n : ℕ} {a : Fin (n + 1) → ℕ} (hcon : Continued a) (h0 : a 0 = 1)
    (h1 : 1 < a 1) :
    (¬ SquareNumber (a 1) →
      ∀ k (hk : k ≤ n), SquareNumber (a ⟨k, by omega⟩) → ∃ j, k = 2 * j) ∧
    (¬ CubeNumber (a 1) →
      ∀ k (hk : k ≤ n), CubeNumber (a ⟨k, by omega⟩) → ∃ j, k = 3 * j) := by
  have ha := unit_pos hcon h0 h1
  obtain ⟨hsq, hcu, -⟩ := proposition_8 hcon h0 h1
  constructor
  · intro hns k hk hk2
    obtain ⟨j, rfl | rfl⟩ : ∃ j, k = 2 * j ∨ k = 2 * j + 1 := ⟨k / 2, by omega⟩
    · exact ⟨j, rfl⟩
    exfalso
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact hns (by rw [← fin_one_eq hk]; exact hk2)
    -- `a (2 * j)` is square [Prop. 9.8], and as it is to `a (2 * j + 1)`, so is `a 1` to
    -- `a 2`: the ratio of a square to a square
    obtain ⟨p, hp, hpe⟩ := hsq j (by omega) hj
    obtain ⟨q, hq, hqe⟩ := hk2
    have h := continued_ratio ha hcon (i := 2 * j) (i' := 2 * j + 1) (j := 1) (j' := 2)
      (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [hpe, hqe, fin_one_eq (by omega)] at h
    -- `a 2` is square, so `a 1` is square [Prop. 8.24]
    exact hns (Elements.Book8.proposition_24 (by omega) (by omega) h1 h.symm.inv
      (hsq 1 (by omega) Nat.one_pos))
  · intro hnc k hk hk3
    obtain ⟨j, rfl | rfl | rfl⟩ : ∃ j, k = 3 * j ∨ k = 3 * j + 1 ∨ k = 3 * j + 2 :=
      ⟨k / 3, by omega⟩
    · exact ⟨j, rfl⟩
    · exfalso
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · exact hnc (by rw [← fin_one_eq hk]; exact hk3)
      -- `a (3 * j)` is cube [Prop. 9.8], and as it is to `a (3 * j + 1)`, so is `a 2`
      -- to `a 3`: the ratio of a cube to a cube; and `a 3` is cube, so `a 2` is
      -- [Props. 7.13, 8.25]
      obtain ⟨p, hp, hpe⟩ := hcu j (by omega) hj
      obtain ⟨q, hq, hqe⟩ := hk3
      have h := continued_ratio ha hcon (i := 3 * j) (i' := 3 * j + 1) (j := 2) (j' := 3)
        (by omega) (by omega) (by omega) (by omega) (by omega)
      rw [hpe, hqe] at h
      have h2 := Elements.Book8.proposition_25 (by omega) (by omega)
        (unit_one_lt hcon h0 h1 (k := 2) (by omega) (by omega)) h.symm.inv
        (hcu 1 (by omega) Nat.one_pos)
      -- `a 1` multiplying itself makes the cube `a 2`, so it is cube [Prop. 9.6]
      rw [unit_two hcon h0 (by omega)] at h2
      exact hnc (proposition_6 h1 h2)
    · exfalso
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · -- `a 1` multiplying itself makes the cube `a 2`, so it is cube [Prop. 9.6]
        rw [show (⟨3 * 0 + 2, by omega⟩ : Fin (n + 1)) = ⟨2, by omega⟩ from rfl,
          unit_two hcon h0 (by omega)] at hk3
        exact hnc (proposition_6 h1 hk3)
      -- as `a (3 * j)` is to `a (3 * j + 2)`, so `a 1` is to `a 3`, the ratio of a cube
      -- to a cube; and `a 3` is cube, so `a 1` is [Props. 7.13, 8.25]
      obtain ⟨p, hp, hpe⟩ := hcu j (by omega) hj
      obtain ⟨q, hq, hqe⟩ := hk3
      have h := continued_ratio ha hcon (i := 3 * j) (i' := 3 * j + 2) (j := 1) (j' := 3)
        (by omega) (by omega) (by omega) (by omega) (by omega)
      rw [hpe, hqe, fin_one_eq (by omega)] at h
      exact hnc (Elements.Book8.proposition_25 (by omega) (by omega) h1 h.symm.inv
        (hcu 1 (by omega) Nat.one_pos))

end Elements.Book9
