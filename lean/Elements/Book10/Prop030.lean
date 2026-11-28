import Elements.Book10.Prop029

namespace Elements.Book10

open Elements.Book5 Elements.Book7 Number

variable {ρ : Length}

/-- To find two rational lines commensurable in square only, the square on the greater
exceeding the square on the lesser by the square on a line incommensurable in length with
the greater. -/
theorem proposition_30 : ∃ x y, BinomialTerms ρ x y ∧ ExceedsIncomm x y := by
  -- two square numbers `64` and `25`, their sum `89` not square [Prop. 10.28 lem. II,
  -- with `16`, `4` and `6`]
  have h89 : ¬ SquareNumber ((25 + 64 : ℕ+) : ℕ) :=
    proposition_28_lemma_2 (a := 16) (b := 4) (d := 6) rfl (by decide) (by decide)
      ⟨8, by decide, rfl⟩
  have sq64 : SquareNumber ((64 : ℕ+) : ℕ) := ⟨8, by decide, rfl⟩
  have sq25 : SquareNumber ((25 : ℕ+) : ℕ) := ⟨5, by decide, rfl⟩
  -- let it be contrived that as `89` is to `64`, so the square on `a` to the square on
  -- `f` [Prop. 10.6 corr.]: as before, `a`, `f` are rational, commensurable in square
  -- only
  obtain ⟨-, f, -, hf⟩ := proposition_6_corollary (25 + 64) 64 ρ
  have haf := inSquareOnly_of_ratio hf (not_square_ratio_of (Or.inr
    ⟨sq64, by decide, h89⟩))
  have hfr : Rational ρ f := Rational.of_inSquare (Rational.self ρ) haf.1.symm
  -- via conversion, as `89` is to `25`, so the square on `a` to the square on `g` [Props.
  -- 5.19 corr., 3.31, 1.47]
  obtain ⟨hfa, g, hg, h₂⟩ := conversion_squares hf
  -- `89` is not to `25` as a square number to a square number: `a`, `g` are
  -- incommensurable in length [Prop. 10.9]
  have hag : ¬ Commensurable ρ g := fun h => not_square_ratio_of (Or.inr
    ⟨sq25, by decide, h89⟩) (by
      obtain ⟨c, d, h'⟩ := proposition_9.mp h
      exact ⟨c, d, Elements.Book5.proposition_11 h₂ h'⟩)
  exact ⟨ρ, f, ⟨Rational.self ρ, hfr, haf, hfa⟩, g, hg, fun h => hag h.symm⟩

end Elements.Book10
