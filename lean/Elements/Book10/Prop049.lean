import Elements.Book10.Prop048

namespace Elements.Book10

open Elements.Book5 Elements.Book7 Number

variable {ρ : Length}

/-- To find a second binomial, relative to a rational line `r` laid out: the numbers as in
10.48, with the lesser term commensurable with `r`. -/
theorem proposition_49 {r : Length} (hr : Rational ρ r) : ∃ l, SecondBinomial ρ r l := by
  -- let it be contrived that as `12` is to `16`, so the square on `r` to the square on
  -- `f` [Prop. 10.6 corr.]; inversely, as `16` to `12`, so the square on `f` to that on
  -- `r` [Prop. 5.7 corr.]
  obtain ⟨-, f, -, hf⟩ := proposition_6_corollary 12 (4 + 12) r
  have hf' := Elements.Book5.proposition_7_corollary hf
  -- `f`, `r` are rational, commensurable in square only, `f` the greater, and `f`, `g`
  -- commensurable in length, as in 10.48
  obtain ⟨hfr, hrf, g, hg, h₂⟩ := terms_of_ratio hf' (not_square_ratio_of (Or.inl ⟨sq_16,
    by decide, not_square_of_between (k := 3) (by decide) (by decide)⟩))
  have hfg : Commensurable f g := proposition_9.mpr ⟨4, 2, h₂.symm⟩
  exact ⟨f + r, f, r, ⟨⟨hr.of_inSquare hfr.1, hr, hfr, hrf⟩, ⟨g, hg, hfg.symm⟩,
    .refl r⟩, rfl⟩

end Elements.Book10
