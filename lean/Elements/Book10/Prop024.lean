import Elements.Book10.Prop023

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- A rectangle contained by medial lines commensurable in length is medial. -/
theorem proposition_24 {x y : Length} (hx : Medial ρ x) (_hy : Medial ρ y)
    (h : Commensurable x y) : MedialArea ρ (rect x y) := by
  -- the square on `x` is medial; as `x` is to `y`, so the square on `x` to the rectangle
  -- [Props. 6.1]: they are commensurable [Prop. 10.11], and the rectangle is medial
  -- [Prop. 10.23 corr.]
  have h₁ := (proposition_11 (proposition_21_lemma x y).1 Length.divisible
    Area.divisible).1 h
  exact proposition_23_corollary hx h₁.symm

end Elements.Book10
