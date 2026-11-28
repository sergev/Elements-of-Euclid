import Elements.Book8.Prop13

namespace Elements.Book8

open Elements.Book7

/-- If a square `c * c` measures a square `d * d`, the side `c` measures the side `d`;
and if the side measures the side, the square measures the square. -/
theorem proposition_14 {c d : ℕ} (hc : 0 < c) (hd : 0 < d) :
    (c * c ∣ d * d → c ∣ d) ∧ (c ∣ d → c * c ∣ d * d) := by
  -- let `c` make `e = d * c` by multiplying `d`: `c * c`, `e`, `d * d` are continuously
  -- proportional in the ratio of `c` to `d` [Prop. 8.11]
  obtain ⟨h₁, h₂⟩ := squares_continued hc hd
  have ha := Nat.mul_pos hc hc
  have he := Nat.mul_pos hd hc
  have hb := Nat.mul_pos hd hd
  have hae : c * c ∶ d * c ∷ d * c ∶ d * d := proportion_trans ha he hc hd h₁ h₂.symm
  constructor
  · -- `c * c` measures `d * d`, so it measures `e` [Prop. 8.7]; and as `c * c` is to `e`,
    -- so `c` to `d`: `c` measures `d` [Def. 7.20]
    intro h
    have hm : c * c ∣ d * c :=
      proposition_7 (three_pos ha he hb) (three_continued ha he hae) h
    exact measures_of_proportion ha he hc hd h₁ hm
  · -- `c` measures `d`, so `c * c` measures `e` [Def. 7.20], and `e` measures `d * d`:
    -- `c * c` measures `d * d`
    intro h
    have hm := measures_of_proportion hc hd ha he h₁.symm h
    exact measures_trans hm (measures_of_proportion ha he he hb hae hm)

end Elements.Book8
