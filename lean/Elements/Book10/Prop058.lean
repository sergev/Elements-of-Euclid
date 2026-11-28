import Elements.Book10.Prop057

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- If an area is contained by a rational line `r` and a fifth binomial, the square root
`z` of the area is the square root of a rational plus a medial area. -/
theorem proposition_58 {r l z : Length} (hr : Rational ρ r) (hl : FifthBinomial ρ r l)
    (hz : sq z = rect r l) : SideRationalMedial ρ z := by
  -- the fifth binomial divided into its terms `x > y`, `y` commensurable with `r`
  -- [Def. 10.II.5], and the construction of 10.54
  obtain ⟨x, y, ⟨⟨hx, hy, hxy, hyx⟩, hexc, hyr⟩, rfl⟩ := hl
  obtain ⟨x₁, x₂, f, m, n, hf, hx₁₂, hr₁₂, -, hm, hn, hmn, hnm, hsum, htwice⟩ :=
    proposition_54_construction r hyx
  -- `x₁`, `x₂` are incommensurable [Prop. 10.18], so `m`, `n` in square
  have h₁ := (proposition_18 hyx hf hx₁₂ hr₁₂).mpr hexc
  -- `x` is incommensurable with `r` [Prop. 10.13]: the squares on `m`, `n`, the rectangle
  -- contained by `r`, `x`, are medial [Prop. 10.21]
  have hxr : ¬ Commensurable x r := fun h' => hxy.2
    (proposition_12 Length.divisible h' hyr)
  have hs : MedialArea ρ (sq m + sq n) := hsum ▸ medial_rect hr hx hxr
  -- `f` is commensurable with `y`, so with `r`: the rectangle contained by `m`, `n`, that
  -- contained by `r`, `f`, is rational [Prop. 10.19]
  have hfr : Commensurable f r :=
    proposition_12 Length.divisible (hf ▸ (double_commensurable f).symm) hyr.symm
  have hrect : RationalArea ρ (rect m n) := hmn ▸ proposition_19 hr
    (hr.of_comm hfr) hfr.symm
  exact ⟨m, n, ⟨construction_incomm_sq h₁ hm hn, hs, hrect, hnm⟩, side_eq_add
    hsum htwice hz⟩

end Elements.Book10
