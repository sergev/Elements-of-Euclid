import Elements.Book10.Prop054

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- In the construction, a piece `x₁` commensurable with `x`, rational and incommensurable
with `r`: the rectangle contained by `r`, `x₁` is medial [Prop. 10.21], and `m` is
medial. -/
theorem construction_medial {r x x₁ m : Length} (hr : Rational ρ r) (hx : Rational ρ x)
    (h₁x : Commensurable x₁ x) (hxr : ¬ Commensurable x r) (hm : sq m = rect r x₁) :
    Medial ρ m := show MedialArea ρ (sq m) by
  rw [hm]; exact medial_rect hr (hx.of_comm h₁x)
    (proposition_13 Length.divisible h₁x.symm hxr)

/-- If an area is contained by a rational line `r` and a second binomial, the square root
`z` of the area is a first bimedial. -/
theorem proposition_55 {r l z : Length} (hr : Rational ρ r) (hl : SecondBinomial ρ r l)
    (hz : sq z = rect r l) : FirstBimedial ρ z := by
  -- the second binomial divided into its terms `x > y`, `y` commensurable with `r`
  -- [Def. 10.II.2], and the construction of 10.54
  obtain ⟨x, y, ⟨⟨hx, hy, hxy, hyx⟩, hexc, hyr⟩, rfl⟩ := hl
  obtain ⟨x₁, x₂, f, m, n, hf, hx₁₂, hr₁₂, -, hm, hn, hmn, hnm, hsum, htwice⟩ :=
    proposition_54_construction r hyx
  -- `x₁`, `x₂` are commensurable [Prop. 10.17], and with `x` [Prop. 10.15], so rational;
  -- `x` is incommensurable in length with `r` [Prop. 10.13], and so `x₁`, `x₂`
  have h₁ := (proposition_17 hyx hf hx₁₂ hr₁₂).mpr hexc
  have h₁x : Commensurable x₁ x := hx₁₂ ▸ (proposition_15.1 h₁).1.symm
  have h₂x : Commensurable x₂ x := hx₁₂ ▸ (proposition_15.1 h₁).2.symm
  have hxr : ¬ Commensurable x r := fun h' => hxy.2
    (proposition_12 Length.divisible h' hyr)
  -- so the rectangles contained by `r` and `x₁`, `x₂`, the squares on `m`, `n`, are
  -- medial [Prop. 10.21]: `m`, `n` are medial
  have hmm := construction_medial hr hx h₁x hxr hm
  have hnm' := construction_medial hr hx h₂x hxr hn
  -- and commensurable in square, `x₁`, `x₂` being commensurable [Props. 6.1, 10.11]
  have hsq : CommensurableInSquare m n := by
    show Commensurable (sq m) (sq n); rw [hm, hn, rect_commensurable_iff]; exact h₁
  -- `f` is commensurable with `y`, so with `r`, and rational: the rectangle contained by
  -- `m`, `n`, that contained by `r`, `f`, is rational [Prop. 10.19]
  have hfr : Commensurable f r :=
    proposition_12 Length.divisible (hf ▸ (double_commensurable f).symm) hyr.symm
  have hrect : RationalArea ρ (rect m n) := hmn ▸ proposition_19 hr
    (hr.of_comm hfr) hfr.symm
  -- `m`, `n` are incommensurable in length, as in 10.54: `m + n` is a first bimedial
  exact ⟨m, n, ⟨hmm, hnm', ⟨hsq, construction_incomm hxy.2 h₁x hf hm hmn⟩, hrect, hnm⟩,
    side_eq_add hsum htwice hz⟩

end Elements.Book10
