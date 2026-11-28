import Elements.Book10.Prop052

namespace Elements.Book10

open Elements.Book5 Elements.Book7 Number

variable {ρ : Length}

/-- To find a sixth binomial, relative to a rational line `r` laid out: the numbers as in
10.51, and `2`, not square, and not to `9` nor to `7` as a square number to a square
number. -/
theorem proposition_53 {r : Length} (hr : Rational ρ r) : ∃ l, SixthBinomial ρ r l := by
  have h2 : ¬ SquareNumber ((2 : ℕ+) : ℕ) := not_square_of_between (k := 1) (by decide)
    (by decide)
  -- as `2` is to `9`, so the square on `r` to the square on `a` [Prop. 10.6 corr.]
  obtain ⟨-, a, -, ha⟩ := proposition_6_corollary 2 (2 + 7) r
  have hra := inSquareOnly_of_ratio ha
    (not_square_ratio_of (Or.inr ⟨sq_9, by decide, h2⟩))
  have har : Rational ρ a := hr.of_inSquare hra.1.symm
  -- as `9` is to `7`, so the square on `a` to the square on `b` [Prop. 10.6 corr.]
  obtain ⟨-, b, -, hb⟩ := proposition_6_corollary (2 + 7) 7 a
  obtain ⟨hab, hba, g, hg, h₂⟩ := terms_of_ratio hb not_square_ratio_9_7
  have hag := (inSquareOnly_of_ratio h₂ not_square_ratio_9_2).2
  -- via equality, as `2` is to `7`, so the square on `r` to the square on `b` [Prop.
  -- 5.22]; `2` is to `7` as `4` to `14`, not as a square number to a square number
  have hrb := inSquareOnly_of_ratio (Elements.Book5.proposition_22' ha hb)
    (not_square_ratio_of_proportion (c := 4) (d := 14) (number_proportion (by decide))
      (not_square_ratio_of (Or.inl ⟨sq_4, by decide,
        not_square_of_between (k := 3) (by decide) (by decide)⟩)))
  exact ⟨a + b, a, b, ⟨⟨har, har.of_inSquare hab.1.symm, hab, hba⟩,
    ⟨g, hg, fun h => hag h.symm⟩, fun h => hra.2 h.symm, fun h => hrb.2 h.symm⟩, rfl⟩

/-- 10.53, lemma: two squares, on `a` and `b`, set out with their sides in straight lines,
and the parallelogram completed: it is the square on `a + b` [Prop. 2.4], the rectangle
contained by `a`, `b` is the mean proportional of the two squares, and the rectangle
contained by `a + b`, `b` the mean proportional of the whole square and the square on
`b` [Props. 6.1, 5.11]. -/
theorem proposition_53_lemma (a b : Length) :
    Proportion (sq a) (rect a b) (rect a b) (sq b) ∧
      Proportion (sq (a + b)) (rect (a + b) b) (rect (a + b) b) (sq b) := by
  -- as `a` is to `b`, so the square on `a` to the rectangle, and the rectangle to the
  -- square on `b` [Prop. 6.1]
  have h₁ := (proposition_21_lemma a b).1
  have h₂ := rect_proportion a b b
  -- and as `a + b` is to `b`, so the whole square to the rectangle, and the rectangle to
  -- the square on `b` [Prop. 6.1]
  have h₃ := (proposition_21_lemma (a + b) b).1
  have h₄ := rect_proportion (a + b) b b
  exact ⟨Elements.Book5.proposition_11 h₁.symm h₂.symm,
    Elements.Book5.proposition_11 h₃.symm h₄.symm⟩

end Elements.Book10
