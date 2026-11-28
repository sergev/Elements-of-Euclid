import Elements.Book8.Prop21

namespace Elements.Book8

open Elements.Book7

/--
Euclid's step in 8.21 and 8.26, for any multitude: the outermost of continuously
proportional numbers `c` are those of the least numbers in the same ratio, `powers x y n`
(8.2), taken some `m` times; and as the one outermost is to the other, so the least.
-/
theorem continued_outer {n : ℕ} {c : Fin (n + 1) → ℕ} (hc : ∀ i, 0 < c i)
    (hcon : Continued c) :
    ∃ x y m, 0 < x ∧ 0 < y ∧ 0 < m ∧
      c 0 ∶ c (Fin.last n) ∷ powers x y n 0 ∶ powers x y n (Fin.last n) ∧
      c 0 = powers x y n 0 * m ∧ c (Fin.last n) = powers x y n (Fin.last n) * m := by
  -- let the least numbers having the same ratio as `c` be taken [Props. 7.33, 8.2]
  obtain ⟨x, y, hx, hy, hxy, hl⟩ := Elements.Book7.proposition_33' (hc 0) (hc 1)
  obtain ⟨hP, hPin, -⟩ := proposition_2 hx hy hl n
  have hcin : ContinuedIn c x y :=
    fun i => proportion_trans (hc _) (hc _) (hc 0) (hc 1) (hcon i) hxy.symm
  -- via equality, as the first of `c` is to the last, so the first of the least to the
  -- last [Prop. 7.14]
  have h14 := (hPin.sameRatios hx hy hc hcin).extremes hP hc (Fin.last n)
  -- these are prime to one another [Props. 7.22, 8.3], so the least [Prop. 7.21], and
  -- they measure the outermost of `c` an equal number of times [Prop. 7.20]
  have hleast := Elements.Book7.proposition_21 (hP 0) (hP _)
    (powers_primeTo hx hy (Elements.Book7.proposition_22 hx hy hl) n)
  obtain ⟨m, h₁, h₂⟩ :=
    Elements.Book7.proposition_20 (hc 0) (hc _) (hP 0) (hP _) hleast h14.symm
  have hm : 0 < m := Nat.pos_of_ne_zero (by
    rintro rfl; have := hc 0; rw [h₁, Nat.mul_zero] at this; omega)
  exact ⟨x, y, m, hx, hy, hm, h14, h₁, h₂⟩

theorem powers_two (x y : ℕ) : powers x y 2 0 = x * x ∧ powers x y 2 2 = y * y :=
  ⟨by show 1 * x * x = _; rw [Nat.one_mul], by show 1 * y * y = _; rw [Nat.one_mul]⟩

theorem powers_three (x y : ℕ) :
    powers x y 3 0 = x * x * x ∧ powers x y 3 3 = y * y * y :=
  ⟨by show 1 * x * x * x = _; rw [Nat.one_mul],
    by show 1 * y * y * y = _; rw [Nat.one_mul]⟩

/--
If three numbers `a`, `b`, `c` are continuously proportional, and the first is square,
the third is also square.

Euclid: `a` and `c` are similar plane numbers [Prop. 8.20], and `a` is square, so `c` is
square [Def. 7.21]. That does not follow: the sides 8.20 finds for a square need not be
equal (`4` is `1 * 4`). The step is 8.21's: `a`, `c` are `x * x`, `y * y` taken `m`
times; `x * x` measures the square `a`, so `x` measures its side [Prop. 8.14], and `m` is
a square. -- Missed by Euclid.
-/
theorem proposition_22 {a b c : ℕ} (hb : 0 < b) (hc : 1 < c) (h : a ∶ b ∷ b ∶ c)
    (ha : SquareNumber a) : SquareNumber c := by
  obtain ⟨p, hp, rfl⟩ := ha
  have ha : 0 < p * p := Nat.mul_pos (by omega) (by omega)
  -- `a`, `c` are the least numbers `x * x`, `y * y` in their ratio, taken `m` times
  -- [Props. 8.2 corollary, 7.20]
  obtain ⟨x, y, m, hx, hy, hm, -, h₁, h₂⟩ :=
    continued_outer (three_pos ha hb (by omega)) (three_continued ha hb h)
  replace h₁ : p * p = x * x * m := by rw [← (powers_two x y).1]; exact h₁
  replace h₂ : c = y * y * m := by rw [← (powers_two x y).2]; exact h₂
  -- `x * x` measures `p * p`, so `x` measures `p` [Prop. 8.14]
  obtain ⟨t, rfl⟩ := (proposition_14 hx (by omega)).1 ⟨m, h₁⟩
  -- so `m` is `t * t` [Prop. 7.16; associativity -- Missed by Euclid.]
  have hmt : m = t * t := Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hx hx) (by
    rw [← h₁]; ring)
  -- and `c` is the square of `y * t` [Prop. 7.16; associativity -- Missed by Euclid.]
  have hct : c = y * t * (y * t) := by rw [h₂, hmt]; ring
  refine ⟨y * t, Nat.lt_of_not_le fun hyt => ?_, hct⟩
  have := Nat.mul_le_mul hyt hyt
  omega

end Elements.Book8
