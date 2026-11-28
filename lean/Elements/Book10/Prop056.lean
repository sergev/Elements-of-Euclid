import Elements.Book10.Prop055

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- If an area is contained by a rational line `r` and a third binomial, the square root
`z` of the area is a second bimedial. -/
theorem proposition_56 {r l z : Length} (hr : Rational ρ r) (hl : ThirdBinomial ρ r l)
    (hz : sq z = rect r l) : SecondBimedial ρ z := by
  -- the third binomial divided into its terms `x > y`, neither commensurable with `r`
  -- [Def. 10.II.3], and the construction of 10.54
  obtain ⟨x, y, ⟨⟨hx, hy, hxy, hyx⟩, hexc, hxr, hyr⟩, rfl⟩ := hl
  obtain ⟨x₁, x₂, f, m, n, hf, hx₁₂, hr₁₂, -, hm, hn, hmn, hnm, hsum, htwice⟩ :=
    proposition_54_construction r hyx
  -- `x₁`, `x₂` are commensurable [Prop. 10.17], and with `x` [Prop. 10.15]: `m`, `n` are
  -- medial, commensurable in square, as in 10.55
  have h₁ := (proposition_17 hyx hf hx₁₂ hr₁₂).mpr hexc
  have h₁x : Commensurable x₁ x := hx₁₂ ▸ (proposition_15.1 h₁).1.symm
  have h₂x : Commensurable x₂ x := hx₁₂ ▸ (proposition_15.1 h₁).2.symm
  have hsq : CommensurableInSquare m n := by
    show Commensurable (sq m) (sq n); rw [hm, hn, rect_commensurable_iff]; exact h₁
  -- `f` is commensurable with `y`, so incommensurable with `r` [Prop. 10.13], and
  -- rational: the rectangle contained by `r`, `f`, that contained by `m`, `n`, is medial
  -- [Prop. 10.21]
  have hfy : Commensurable f y := hf ▸ (double_commensurable f).symm
  have hrect : MedialArea ρ (rect m n) := hmn ▸ medial_rect hr (hy.of_comm hfy)
    (proposition_13 Length.divisible hfy.symm hyr)
  exact ⟨m, n, ⟨construction_medial hr hx h₁x hxr hm, construction_medial hr
    hx h₂x hxr hn,
    ⟨hsq, construction_incomm hxy.2 h₁x hf hm hmn⟩, hrect, hnm⟩, side_eq_add
      hsum htwice hz⟩

end Elements.Book10
