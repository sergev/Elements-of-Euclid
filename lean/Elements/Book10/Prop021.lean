import Elements.Book10.Prop020

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- The rectangle contained by rational lines commensurable in square only is irrational,
and so is its square root, a line whose square is equal to it: let it be called medial
(`MedialArea`, `Medial`). -/
theorem proposition_21 {x y : Length} (hx : Rational ρ x) (_hy : Rational ρ y)
    (h : InSquareOnly x y) :
    ¬ RationalArea ρ (rect x y) ∧ ∀ z, sq z = rect x y → ¬ Rational ρ z := by
  -- the square on `x` is rational [Def. 10.4]; `x` is incommensurable in length with `y`,
  -- and as `x` is to `y`, so the square on `x` to the rectangle [Prop. 6.1]: they are
  -- incommensurable [Prop. 10.11]
  have h₁ : Proportion (sq x) (rect y x) x y := rect_proportion x y x
  rw [rect_comm] at h₁
  have h₂ := (proposition_11 h₁.symm Length.divisible Area.divisible).2 h.2
  -- the square on `x` is rational, so the rectangle is irrational [Def. 10.4]
  have h₃ := hx.sq_rational.not_of_not_comm h₂
  -- and its square root is irrational [Def. 10.4]
  exact ⟨h₃, fun z hz hzr => h₃ (hz ▸ hzr.sq_rational)⟩

/-- 10.21, lemma: as the first of two lines is to the second, so the square on the first
to the rectangle contained by the two; and as the rectangle to the square on the first,
so the second to the first [Prop. 6.1]. -/
theorem proposition_21_lemma (a b : Length) :
    Proportion a b (sq a) (rect a b) ∧ Proportion (rect b a) (sq a) b a := by
  have h := rect_proportion a b a
  rw [rect_comm b a] at h
  exact ⟨h.symm, by rw [rect_comm]; exact Elements.Book5.proposition_7_corollary h⟩

end Elements.Book10
