import Elements.Book8.Prop14

namespace Elements.Book8

open Elements.Book7

/-- If a cube `c * c * c` measures a cube `d * d * d`, the side `c` measures the side
`d`; and if the side measures the side, the cube measures the cube. -/
theorem proposition_15 {c d : ℕ} (hc : 0 < c) (hd : 0 < d) :
    (c * c * c ∣ d * d * d → c ∣ d) ∧ (c ∣ d → c * c * c ∣ d * d * d) := by
  -- `c * c * c`, `h = d * c * c`, `k = d * c * d`, `d * d * d` are continuously
  -- proportional in the ratio of `c` to `d` [Prop. 8.12]
  obtain ⟨h₁, h₂, h₃⟩ := cubes_continued hc hd
  have ha := Nat.mul_pos (Nat.mul_pos hc hc) hc
  have hh := Nat.mul_pos (Nat.mul_pos hd hc) hc
  have hk := Nat.mul_pos (Nat.mul_pos hd hc) hd
  have hb := Nat.mul_pos (Nat.mul_pos hd hd) hd
  have hah := proportion_trans ha hh hc hd h₁ h₂.symm
  have hhk := proportion_trans hh hk hc hd h₂ h₃.symm
  constructor
  · -- the cube measures `d * d * d`, so it measures `h` [Prop. 8.7]; and as it is to `h`,
    -- so `c` to `d` [Def. 7.20]
    intro h
    have hm : c * c * c ∣ d * c * c :=
      proposition_7 (four_pos ha hh hk hb) (four_continued ha hh hk hb hah hhk) h
    exact measures_of_proportion ha hh hc hd h₁ hm
  · -- `c` measures `d`, so the cube measures `h` [Def. 7.20]; and so on to `d * d * d`
    intro h
    have hm₁ := measures_of_proportion hc hd ha hh h₁.symm h
    have hm₂ := measures_of_proportion hc hd hh hk h₂.symm h
    have hm₃ := measures_of_proportion hc hd hk hb h₃.symm h
    exact measures_trans hm₁ (measures_trans hm₂ hm₃)

end Elements.Book8
