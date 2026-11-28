import Elements.Book10.Prop067

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- For terms in the same ratio, `x` commensurable with `x'`, the sums of the squares are
commensurable: as the square on `x` is to that on `x'`, so the square on `y` to that on
`y'` [Props. 5.16, 6.22], and so the sums [Prop. 5.12]; and the squares on `x`, `x'` are
commensurable [Props. 10.9 corr., 10.11]. Euclid composes the ratios with the whole
instead. -/
theorem squares_comm_of_terms {x y x' y' : Length} (hp : Proportion x y x' y')
    (hx : Commensurable x x') : Commensurable (sq x + sq y) (sq x' + sq y') := by
  have h₁ := proportion_add (proportion_sq.mp (Elements.Book5.proposition_16 hp))
  exact (proposition_11 h₁ Area.divisible Area.divisible).1 (proposition_9_corollary hx)

/-- For terms in the same ratio, incommensurable in square, so are the others [Props.
6.22, 10.11]. -/
theorem notInSquare_of_terms {x y x' y' : Length} (hp : Proportion x y x' y')
    (h : ¬ CommensurableInSquare x y) : ¬ CommensurableInSquare x' y' :=
  (proposition_11 (proportion_sq.mp hp) Area.divisible Area.divisible).2 h

/-- A line commensurable in length with a major line is a major line. -/
theorem proposition_68 {l l' : Length} (hl : Major ρ l) (h : Commensurable l l') :
    Major ρ l' :=
  -- the terms are incommensurable in square, the squares commensurable with the squares,
  -- so rational, and the rectangles with the rectangles, so medial [Prop. 10.23 corr.]
  Transfers.sum (fun ⟨h₁, h₂, h₃, h₄⟩ hp hx _ =>
    ⟨notInSquare_of_terms hp h₁, h₂.of_comm (squares_comm_of_terms hp hx).symm,
      proposition_23_corollary h₃ (rect_comm_of_terms hp hx).symm,
      lt_of_proportion hp h₄⟩) h hl

end Elements.Book10
