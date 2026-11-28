import Elements.Book7.Prop14

namespace Elements.Book7

/--
If the unit measures `b` as many times as `d` measures `e` (`n` times), then, alternately,
the unit measures `d` as many times as `b` measures `e`.
-/
theorem proposition_15 {b d e n : ℕ} (hd : 0 < d) (hn : 0 < n) (h₁ : b = 1 * n)
    (h₂ : e = d * n) : ∃ m, d = 1 * m ∧ e = b * m := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  -- `b` divided into its units, and `e` into as many numbers equal to `d`: as each unit
  -- is to each `d`, so are all of them [Prop. 7.12]
  have h := proposition_12 (a := fun _ : Fin (k + 1) => 1) (b := fun _ => d)
    (fun _ => Nat.one_pos) (fun _ => hd) (fun _ => Proportion.refl Nat.one_pos hd)
  rw [sum_const, sum_const, ← h₁, ← h₂] at h
  -- so the unit measures `d` as many times as `b` measures `e` [Def. 7.20]
  obtain ⟨p, q, x, f, -, -, h1, rfl, rfl, rfl⟩ := proportion_iff.mp h
  obtain ⟨rfl, rfl⟩ : x = 1 ∧ p = 1 := ⟨Nat.eq_one_of_mul_eq_one_right h1.symm,
    Nat.eq_one_of_mul_eq_one_left h1.symm⟩
  exact ⟨q, rfl, by rw [Nat.mul_one]⟩

end Elements.Book7
