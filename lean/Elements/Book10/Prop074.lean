import Elements.Book10.Prop073

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- If a medial line `y`, commensurable in square only with the whole `x` and containing a
rational area with it, is taken from the medial `x`, the remainder `l` is irrational: let
it be called a first apotome of a medial (`FirstApotomeOfMedial`). -/
theorem proposition_74 {l x y : Length} (hx : Medial ρ x) (_hy : Medial ρ y)
    (h : InSquareOnly x y) (hr : RationalArea ρ (rect x y)) (hl : l + y = x) :
    ¬ Rational ρ l := by
  -- the squares are medial, twice the rectangle rational: they are incommensurable; so
  -- twice the rectangle with the remaining square on `l` [Props. 2.7, 10.16]; it is
  -- rational, so the square on `l` is irrational, and `l` [Def. 10.4]
  have h₁ : ¬ Commensurable (sq x + sq y) ((2 : ℕ+) • rect x y) := fun h' =>
    (proposition_23_corollary hx (proposition_15.1 h.1).1).not_rational
      (hr.twice.of_comm h')
  exact fun h' => hr.twice.not_of_not_comm (twice_rect_incomm_sq_sub hl h₁) h'.sq_rational

end Elements.Book10
