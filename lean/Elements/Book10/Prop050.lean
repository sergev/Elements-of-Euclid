import Elements.Book10.Prop049

namespace Elements.Book10

open Elements.Book5 Elements.Book7 Number

variable {ρ : Length}

/-- To find a third binomial, relative to a rational line `r` laid out: the numbers as in
10.48, and `2`, not square, and not to `16` nor to `12` as a square number to a square
number. -/
theorem proposition_50 {r : Length} (hr : Rational ρ r) : ∃ l, ThirdBinomial ρ r l := by
  have h2 : ¬ SquareNumber ((2 : ℕ+) : ℕ) := not_square_of_between (k := 1) (by decide)
    (by decide)
  -- let it be contrived that as `2` is to `16`, so the square on `r` to the square on `a`
  -- [Prop. 10.6 corr.]: `a` is rational, incommensurable in length with `r` [Props. 10.6,
  -- 10.9]
  obtain ⟨-, a, -, ha⟩ := proposition_6_corollary 2 (4 + 12) r
  have hra := inSquareOnly_of_ratio ha
    (not_square_ratio_of (Or.inr ⟨sq_16, by decide, h2⟩))
  have har : Rational ρ a := hr.of_inSquare hra.1.symm
  -- and as `16` is to `12`, so the square on `a` to the square on `b` [Prop. 10.6 corr.]:
  -- `a`, `b` are rational, commensurable in square only, and the square on `a` exceeds
  -- that on `b` by the square on a line commensurable with `a`, as in 10.48
  obtain ⟨-, b, -, hb⟩ := proposition_6_corollary (4 + 12) 12 a
  obtain ⟨hab, hba, g, hg, h₂⟩ := terms_of_ratio hb (not_square_ratio_of (Or.inl ⟨sq_16,
    by decide, not_square_of_between (k := 3) (by decide) (by decide)⟩))
  have hag : Commensurable a g := proposition_9.mpr ⟨4, 2, h₂.symm⟩
  -- via equality, as `2` is to `12`, so the square on `r` to the square on `b` [Prop.
  -- 5.22]: `2` is to `12` as `6` to `36`, not as a square number to a square number, so
  -- `r`, `b` are incommensurable in length [Prop. 10.9]
  have h₃ := Elements.Book5.proposition_22' ha hb
  have hrb := inSquareOnly_of_ratio h₃ (not_square_ratio_of_proportion (c := 6) (d := 36)
    (number_proportion (by decide)) (not_square_ratio_of (Or.inr ⟨sq_36, by decide,
      not_square_of_between (k := 2) (by decide) (by decide)⟩)))
  exact ⟨a + b, a, b, ⟨⟨har, har.of_inSquare hab.1.symm, hab, hba⟩, ⟨g, hg, hag.symm⟩,
    fun h => hra.2 h.symm, fun h => hrb.2 h.symm⟩, rfl⟩

end Elements.Book10
