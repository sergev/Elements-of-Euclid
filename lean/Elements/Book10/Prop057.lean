import Elements.Book10.Prop056

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- In the construction, if `x₁`, `x₂` are incommensurable, `m`, `n` are incommensurable
in square [Props. 6.1, 10.11]. -/
theorem construction_incomm_sq {r x₁ x₂ m n : Length} (h : ¬ Commensurable x₁ x₂)
    (hm : sq m = rect r x₁) (hn : sq n = rect r x₂) : ¬ CommensurableInSquare m n := by
  show ¬ Commensurable (sq m) (sq n); rw [hm, hn, rect_commensurable_iff]; exact h

/-- If an area is contained by a rational line `r` and a fourth binomial, the square root
`z` of the area is a major line. -/
theorem proposition_57 {r l z : Length} (hr : Rational ρ r) (hl : FourthBinomial ρ r l)
    (hz : sq z = rect r l) : Major ρ z := by
  -- the fourth binomial divided into its terms `x > y`, `x` commensurable with `r`
  -- [Def. 10.II.4], and the construction of 10.54
  obtain ⟨x, y, ⟨⟨hx, hy, hxy, hyx⟩, hexc, hxr⟩, rfl⟩ := hl
  obtain ⟨x₁, x₂, f, m, n, hf, hx₁₂, hr₁₂, -, hm, hn, hmn, hnm, hsum, htwice⟩ :=
    proposition_54_construction r hyx
  -- the square on `x` exceeds that on `y` by the square on a line incommensurable with
  -- `x`: `x₁`, `x₂` are incommensurable [Prop. 10.18], so `m`, `n` in square
  have h₁ := (proposition_18 hyx hf hx₁₂ hr₁₂).mpr hexc
  -- the squares on `m`, `n` are the rectangle contained by `r`, `x`, rational [Prop.
  -- 10.19]
  have hs : RationalArea ρ (sq m + sq n) := hsum ▸ proposition_19 hr hx hxr.symm
  -- `y` is incommensurable with `r` [Prop. 10.13], and so `f`: the rectangle contained by
  -- `m`, `n`, that contained by `r`, `f`, is medial [Prop. 10.21]
  have hyr : ¬ Commensurable y r := fun h' => hxy.2
    (proposition_12 Length.divisible hxr h')
  have hfy : Commensurable f y := hf ▸ (double_commensurable f).symm
  have hrect : MedialArea ρ (rect m n) := hmn ▸ medial_rect hr (hy.of_comm hfy)
    (proposition_13 Length.divisible hfy.symm hyr)
  exact ⟨m, n, ⟨construction_incomm_sq h₁ hm hn, hs, hrect, hnm⟩, side_eq_add
    hsum htwice hz⟩

end Elements.Book10
