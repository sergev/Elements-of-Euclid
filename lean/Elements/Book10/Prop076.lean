import Elements.Book10.Prop075

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- If a line `y`, incommensurable in square with the whole `x`, the squares on them
rational and the rectangle medial, is taken from `x`, the remainder `l` is irrational: let
it be called a minor line (`Minor`). The mirror of 10.39. -/
theorem proposition_76 {l x y : Length} (_h : ¬ CommensurableInSquare x y)
    (hs : RationalArea ρ (sq x + sq y)) (hr : MedialArea ρ (rect x y)) (hl : l + y = x) :
    ¬ Rational ρ l := by
  -- the squares, rational, are incommensurable with twice the rectangle, medial; via
  -- conversion, with the remaining square on `l` [Props. 2.7, 10.16]: it is irrational,
  -- and `l` [Def. 10.4]
  have h₁ : ¬ Commensurable (sq x + sq y) ((2 : ℕ+) • rect x y) :=
    fun h' => hr.twice.not_rational (hs.of_comm h'.symm)
  exact fun h' => hs.not_of_not_comm (squares_incomm_sq_sub hl h₁) h'.sq_rational

end Elements.Book10
