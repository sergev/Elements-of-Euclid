import Elements.Book8.Prop11

namespace Elements.Book8

open Elements.Book7

/-- Euclid's numbers for 8.12: `c * c * c`, `h = d * c * c`, `k = d * c * d`,
`d * d * d` are continuously proportional in the ratio of `c` to `d`: `e = c * c`,
`f = d * c`, `g = d * d`, and `c`, `d` multiplying `f` make `h`, `k`. -/
theorem cubes_continued {c d : ℕ} (hc : 0 < c) (hd : 0 < d) :
    c * c * c ∶ d * c * c ∷ c ∶ d ∧ d * c * c ∶ d * c * d ∷ c ∶ d ∧
      d * c * d ∶ d * d * d ∷ c ∶ d := by
  obtain ⟨hef, hfg⟩ := squares_continued hc hd
  have he := Nat.mul_pos hc hc
  have hf := Nat.mul_pos hd hc
  have hg := Nat.mul_pos hd hd
  refine ⟨?_, ?_, ?_⟩
  · -- `c` has made `c * c * c`, `h` by multiplying `e`, `f`: as `e` is to `f`, so they
    -- [Prop. 7.17]; and `e` is to `f` as `c` to `d`
    exact proportion_trans (Nat.mul_pos he hc) (Nat.mul_pos hf hc) he hf
      (Elements.Book7.proposition_17 hc he hf).symm hef
  · -- `c`, `d` have made `h`, `k` by multiplying `f` [Prop. 7.18]
    exact (Elements.Book7.proposition_18 hc hd hf).symm
  · -- `d` has made `k`, `d * d * d` by multiplying `f`, `g` [Prop. 7.17]; and `f` is to
    -- `g` as `c` to `d`
    exact proportion_trans (Nat.mul_pos hf hd) (Nat.mul_pos hg hd) hf hg
      (Elements.Book7.proposition_17 hd hf hg).symm hfg

/--
There exist two numbers in mean proportion to two cube numbers `c * c * c`, `d * d * d`,
and cube has to cube the cubed ratio of side `c` to side `d`. The sides may be the unit.
-/
theorem proposition_12 {c d : ℕ} (hc : 0 < c) (hd : 0 < d) :
    FallBetween 2 (c * c * c) (d * d * d) ∧ CubedRatio (c * c * c) (d * d * d) c d := by
  obtain ⟨h₁, h₂, h₃⟩ := cubes_continued hc hd
  have ha := Nat.mul_pos (Nat.mul_pos hc hc) hc
  have hh := Nat.mul_pos (Nat.mul_pos hd hc) hc
  have hk := Nat.mul_pos (Nat.mul_pos hd hc) hd
  have hb := Nat.mul_pos (Nat.mul_pos hd hd) hd
  -- as `c` is to `d`, so `c * c * c` to `h`, and `h` to `k`, and `k` to `d * d * d`
  refine ⟨fallBetween_two ha hh hk hb (proportion_trans ha hh hc hd h₁ h₂.symm)
    (proportion_trans hh hk hc hd h₂ h₃.symm), _, _, hh, hk, h₁, h₂, h₃⟩

end Elements.Book8
