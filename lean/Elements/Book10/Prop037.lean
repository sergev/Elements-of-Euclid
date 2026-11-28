import Elements.Book10.Prop036

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- If two medial lines commensurable in square only, containing a rational area, are
added together, the whole is irrational: let it be called a first bimedial
(`FirstBimedial`). -/
theorem proposition_37 {x y : Length} (_hx : Medial ρ x) (_hy : Medial ρ y)
    (h : InSquareOnly x y) (hr : RationalArea ρ (rect x y)) : ¬ Rational ρ (x + y) := by
  -- the squares are incommensurable with twice the rectangle [Prop. 10.36]; so the square
  -- on the whole [Prop. 2.4] with twice the rectangle [Prop. 10.16], and with the
  -- rectangle [Props. 10.6, 10.13]
  have h₁ := (proposition_16.1 h.squares_twice_rect).2
  rw [← sq_add] at h₁
  have h₂ := proposition_13 Area.divisible (twice_commensurable (rect x y))
    (fun h' => h₁ h'.symm)
  -- the rectangle is rational: so the square on the whole is irrational, and the whole
  -- [Def. 10.4]
  exact fun h' => hr.not_of_not_comm h₂ h'.sq_rational

end Elements.Book10
