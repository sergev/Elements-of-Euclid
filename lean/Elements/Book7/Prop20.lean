import Elements.Book7.Prop19

namespace Elements.Book7

/--
The least numbers `c`, `d` of those having the same ratio measure those having the same
ratio as them, `a` and `b`, an equal number of times, the greater the greater and the
lesser the lesser.
-/
theorem proposition_20 {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hl : Least c d) (h : c ∶ d ∷ a ∶ b) : ∃ n, a = c * n ∧ b = d * n := by
  -- whichever `c` is of `a`, `d` is the same of `b` [Def. 7.20, Prop. 7.13]
  rcases proposition_13 hc hd ha hb h with ⟨n, hn, h₁, h₂⟩ | ⟨n, ⟨-, h₁⟩, ⟨-, h₂⟩⟩ |
    ⟨m, n, ⟨hm, -, x, h₁, -⟩, ⟨-, -, y, h₂, -⟩⟩ |
    ⟨m, n, ⟨-, hmn, x, ha', h₁⟩, ⟨-, -, y, hb', h₂⟩⟩
  · -- `a`, `b` are not less than `c`, `d`, so `c` is `a`, and `d` is `b`
    rcases Nat.lt_or_ge 1 n with hn1 | hn1
    · exact absurd ⟨h₁ ▸ lt_mul ha hn1, h₂ ▸ lt_mul hb hn1⟩ (hl a b ha hb h.symm)
    · obtain rfl : n = 1 := by omega
      rw [Nat.mul_one] at h₁ h₂
      exact ⟨1, by rw [h₁, Nat.mul_one], by rw [h₂, Nat.mul_one]⟩
  · -- `c` is part of `a`, and `d` the same part of `b`
    exact ⟨n, h₁, h₂⟩
  · -- `c` is not parts of `a`: divided into `m` parts `x` of `a`, and `d` into the parts
    -- `y` of `b`, as `x` is to `y` so `c` is to `d` [Prop. 7.12]
    have hx : 0 < x := Nat.pos_of_ne_zero (by rintro rfl; rw [Nat.zero_mul] at h₁; omega)
    have hy : 0 < y := Nat.pos_of_ne_zero (by rintro rfl; rw [Nat.zero_mul] at h₂; omega)
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have h' := proposition_12 (a := fun _ : Fin (k + 1) => x) (b := fun _ => y)
      (fun _ => hx) (fun _ => hy) (fun _ => Proportion.refl hx hy)
    rw [sum_const, sum_const, ← h₁, ← h₂] at h'
    -- `x`, `y` are less than `c`, `d`: impossible
    exact absurd ⟨h₁ ▸ lt_mul hx hm, h₂ ▸ lt_mul hy hm⟩ (hl x y hx hy h')
  · -- nor are `a`, `b` parts of `c`, `d`, being less than them in the same ratio
    have hx : 0 < x := Nat.pos_of_ne_zero (by rintro rfl; rw [Nat.zero_mul] at ha'; omega)
    have hy : 0 < y := Nat.pos_of_ne_zero (by rintro rfl; rw [Nat.zero_mul] at hb'; omega)
    refine absurd ⟨?_, ?_⟩ (hl a b ha hb h.symm)
    · rw [ha', h₁]
      exact Nat.mul_lt_mul_of_pos_left hmn hx
    · rw [hb', h₂]
      exact Nat.mul_lt_mul_of_pos_left hmn hy

end Elements.Book7
