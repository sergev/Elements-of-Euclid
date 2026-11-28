import Elements.Book10.Prop076

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- If a line `y`, incommensurable in square with the whole `x`, the squares on them
medial and twice the rectangle rational, is taken from `x`, the remainder `l` is
irrational: let it be called that which makes with a rational area a medial whole
(`MedialWholeWithRational`). The mirror of 10.40. -/
theorem proposition_77 {l x y : Length} (_h : ¬ CommensurableInSquare x y)
    (hs : MedialArea ρ (sq x + sq y)) (hr : RationalArea ρ (rect x y)) (hl : l + y = x) :
    ¬ Rational ρ l := by
  -- the squares are incommensurable with twice the rectangle; so the remaining square on
  -- `l` with twice the rectangle [Props. 2.7, 10.16], which is rational: it is
  -- irrational, and `l` [Def. 10.4]
  have h₁ : ¬ Commensurable (sq x + sq y) ((2 : ℕ+) • rect x y) :=
    fun h' => hs.not_rational (hr.twice.of_comm h')
  exact fun h' => hr.twice.not_of_not_comm (twice_rect_incomm_sq_sub hl h₁) h'.sq_rational

end Elements.Book10
