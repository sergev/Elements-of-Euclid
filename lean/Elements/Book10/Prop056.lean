import Elements.Book10.Prop055

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- The terms of 10.56: the terms `x > y` of a third binomial, applied to a rational line
`r`, give terms `m > n` of a second bimedial, the squares on them the rectangle contained
by `r`, `x`, twice the rectangle contained by them that contained by `r`, `y`. Shared with
10.93. -/
theorem proposition_56_terms {r x y : Length} (hr : Rational ρ r)
    (h : ThirdTerms ρ r x y) :
    ∃ m n, SecondBimedialTerms ρ m n ∧ sq m + sq n = rect r x ∧
      (2 : ℕ+) • rect m n = rect r y := by
  -- the third binomial divided into its terms `x > y`, neither commensurable with `r`
  -- [Def. 10.II.3], and the construction of 10.54
  obtain ⟨⟨hx, hy, hxy, hyx⟩, hexc, hxr, hyr⟩ := h
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
    ⟨hsq, construction_incomm hxy.2 h₁x hf hm hmn⟩, hrect, hnm⟩, hsum, htwice⟩

/-- If an area is contained by a rational line `r` and a third binomial, the square root
`z` of the area is a second bimedial. -/
theorem proposition_56 {r l z : Length} (hr : Rational ρ r) (hl : ThirdBinomial ρ r l)
    (hz : sq z = rect r l) : SecondBimedial ρ z := by
  obtain ⟨x, y, h, rfl⟩ := hl
  obtain ⟨m, n, hmn, hsum, htwice⟩ := proposition_56_terms hr h
  -- `m + n` is the square root of the area [Props. 10.53 lem., 2.4]
  exact ⟨m, n, hmn, side_eq_add hsum htwice hz⟩

end Elements.Book10
