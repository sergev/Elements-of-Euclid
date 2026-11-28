import Elements.Book10.Prop051

namespace Elements.Book10

open Elements.Book5 Elements.Book7 Number

variable {ρ : Length}

/-- To find a fifth binomial, relative to a rational line `r` laid out: the numbers as in
10.51, with the lesser term commensurable with `r`. -/
theorem proposition_52 {r : Length} (hr : Rational ρ r) : ∃ l, FifthBinomial ρ r l := by
  -- let it be contrived that as `7` is to `9`, so the square on `r` to the square on `f`
  -- [Prop. 10.6 corr.]; inversely [Prop. 5.7 corr.], and as in 10.51
  obtain ⟨-, f, -, hf⟩ := proposition_6_corollary 7 (2 + 7) r
  obtain ⟨hfr, hrf, g, hg, h₂⟩ :=
    terms_of_ratio (Elements.Book5.proposition_7_corollary hf) not_square_ratio_9_7
  have hfg := (inSquareOnly_of_ratio h₂ not_square_ratio_9_2).2
  exact ⟨f + r, f, r, ⟨⟨hr.of_inSquare hfr.1, hr, hfr, hrf⟩,
    ⟨g, hg, fun h => hfg h.symm⟩, .refl r⟩, rfl⟩

end Elements.Book10
