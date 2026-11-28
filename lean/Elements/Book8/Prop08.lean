import Elements.Book8.Prop07

namespace Elements.Book8

open Elements.Book7

/--
If between two numbers `a`, `b` there fall `n` numbers in continued proportion, then as
many will fall in continued proportion between any two numbers `e`, `f` having the same
ratio. Euclid has two numbers fall between; the argument is the same for any multitude.
-/
theorem proposition_8 {n a b e f : ℕ} (he : 0 < e) (hf : 0 < f) (h : FallBetween n a b)
    (hab : a ∶ b ∷ e ∶ f) : FallBetween n e f := by
  obtain ⟨c, hc, hcon, rfl, rfl⟩ := h
  -- as many as `c` are, let so many least numbers `g` having the same ratio be taken
  -- [Props. 7.33, 8.2]
  obtain ⟨r, s, hr, hs, hrs, hlrs⟩ := Elements.Book7.proposition_33' (hc 0) (hc 1)
  obtain ⟨hg, hgin, hgl⟩ := proposition_2 hr hs hlrs (n + 1)
  have hcin : ContinuedIn c r s :=
    fun i => proportion_trans (hc _) (hc _) (hc 0) (hc 1) (hcon i) hrs.symm
  -- the outermost of `g` are prime to one another [Prop. 8.3]
  have hprime := proposition_3 hg (hgin.continued hg hr hs) hgl
  -- via equality, as the first of `c` is to the last, so the first of `g` to the last
  -- [Prop. 7.14], and so `e` to `f`
  have h14 := (hgin.sameRatios hr hs hc hcin).extremes hg hc (Fin.last _)
  have hgef := proportion_trans (hg 0) (hg _) (hc 0) (hc _) h14.symm hab
  -- prime, so the least [Prop. 7.21]: the first of `g` measures `e` as many times, `k`,
  -- as the last measures `f` [Prop. 7.20]
  obtain ⟨k, hk₁, hk₂⟩ := Elements.Book7.proposition_20 he hf (hg 0) (hg _)
    (Elements.Book7.proposition_21 (hg 0) (hg _) hprime) hgef
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; rw [Nat.mul_zero] at hk₁; omega)
  -- as many times, let each of `g` measure the numbers `d`: they are in the same ratio as
  -- `g` [Def. 7.20, Prop. 7.17], so continuously proportional
  have hd : ∀ i, 0 < powers r s (n + 1) i * k := fun i => Nat.mul_pos (hg i) hk
  have hdin : ContinuedIn (fun i => powers r s (n + 1) i * k) r s := fun i =>
    proportion_trans (hd _) (hd _) (hg _) (hg _)
      (Elements.Book7.proposition_17 hk (hg _) (hg _)).symm (hgin i)
  exact ⟨_, hd, hdin.continued hd hr hs, hk₁.symm, hk₂.symm⟩

end Elements.Book8
