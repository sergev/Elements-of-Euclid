import Elements.Book8.Prop22

namespace Elements.Book8

open Elements.Book7

/--
If four numbers `a`, `b`, `c`, `d` are continuously proportional, and the first is cube,
the fourth is also cube.

Euclid: `a` and `d` are similar solid numbers [Prop. 8.21], and `a` is cube, so `d` is
cube [Def. 7.21]. As in 8.22, that does not follow; the step is 8.21's: `a`, `d` are
`x * x * x`, `y * y * y` taken `m` times, `x` measures the side of `a` [Prop. 8.15], and
`m` is a cube. -- Missed by Euclid.
-/
theorem proposition_23 {a b c d : ℕ} (hb : 0 < b) (hc : 0 < c) (hd : 1 < d)
    (h₁ : a ∶ b ∷ b ∶ c) (h₂ : b ∶ c ∷ c ∶ d) (ha : CubeNumber a) : CubeNumber d := by
  obtain ⟨p, hp, rfl⟩ := ha
  have ha : 0 < p * p * p := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  -- `a`, `d` are the least numbers `x * x * x`, `y * y * y` in their ratio, taken `m`
  -- times [Props. 8.2 corollary, 7.20]
  obtain ⟨x, y, m, hx, hy, hm, -, hA, hD⟩ :=
    continued_outer (four_pos ha hb hc (by omega))
      (four_continued ha hb hc (by omega) h₁ h₂)
  replace hA : p * p * p = x * x * x * m := by rw [← (powers_three x y).1]; exact hA
  replace hD : d = y * y * y * m := by rw [← (powers_three x y).2]; exact hD
  -- `x * x * x` measures `p * p * p`, so `x` measures `p` [Prop. 8.15]
  obtain ⟨t, rfl⟩ := (proposition_15 hx (by omega)).1 ⟨m, hA⟩
  -- so `m` is `t * t * t` [Prop. 7.16; associativity -- Missed by Euclid.]
  have hmt : m = t * t * t :=
    Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (Nat.mul_pos hx hx) hx) (by rw [← hA]; ring)
  -- and `d` is the cube of `y * t` [Prop. 7.16; associativity -- Missed by Euclid.]
  have hdt : d = y * t * (y * t) * (y * t) := by rw [hD, hmt]; ring
  refine ⟨y * t, Nat.lt_of_not_le fun hyt => ?_, hdt⟩
  have := Nat.mul_le_mul (Nat.mul_le_mul hyt hyt) hyt
  omega

end Elements.Book8
