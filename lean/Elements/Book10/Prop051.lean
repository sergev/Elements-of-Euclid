import Elements.Book10.Prop050

namespace Elements.Book10

open Elements.Book5 Elements.Book7 Number

variable {ρ : Length}

/-- The numbers of 10.51–10.53: `2` and `7`, their sum `9` not to `2` nor to `7` as a
square number to a square number. -/
theorem not_square_ratio_9_7 :
    ¬ ∃ c d : ℕ+, Proportion ((2 + 7 : ℕ+) : Number) ((7 : ℕ+) : Number)
      ((c : Number) * c)
      ((d : Number) * d) :=
  not_square_ratio_of (Or.inl ⟨sq_9, by decide,
    not_square_of_between (k := 2) (by decide) (by decide)⟩)

theorem not_square_ratio_9_2 :
    ¬ ∃ c d : ℕ+, Proportion ((2 + 7 : ℕ+) : Number) ((2 : ℕ+) : Number)
      ((c : Number) * c)
      ((d : Number) * d) :=
  not_square_ratio_of (Or.inl ⟨sq_9, by decide,
    not_square_of_between (k := 1) (by decide) (by decide)⟩)

/-- To find a fourth binomial, relative to a rational line `r` laid out: the numbers `2`,
`7`, their sum `9` not to either as a square number to a square number. -/
theorem proposition_51 {r : Length} (hr : Rational ρ r) : ∃ l, FourthBinomial ρ r l := by
  -- let it be contrived that as `9` is to `7`, so the square on `r` to the square on `f`
  -- [Prop. 10.6 corr.]: `r`, `f` are rational, commensurable in square only [Props. 10.6,
  -- 10.9]; via conversion, `9` is to `2` as the square on `r` to the square on `g` [Prop.
  -- 5.19 corr.], so `r`, `g` are incommensurable in length [Prop. 10.9]
  obtain ⟨-, f, -, hf⟩ := proposition_6_corollary (2 + 7) 7 r
  obtain ⟨hrf, hfr, g, hg, h₂⟩ := terms_of_ratio hf not_square_ratio_9_7
  have hrg := (inSquareOnly_of_ratio h₂ not_square_ratio_9_2).2
  exact ⟨r + f, r, f, ⟨⟨hr, hr.of_inSquare hrf.1.symm, hrf, hfr⟩,
    ⟨g, hg, fun h => hrg h.symm⟩, .refl r⟩, rfl⟩

end Elements.Book10
