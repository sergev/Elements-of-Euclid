import Elements.Book10.Prop077

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- If a line `y`, incommensurable in square with the whole `x`, the squares on them
medial, twice the rectangle medial and incommensurable with the squares, is taken from
`x`, the remainder `l` is irrational: let it be called that which makes with a medial area
a medial whole (`MedialWholeWithMedial`). The mirror of 10.41. -/
theorem proposition_78 {l x y : Length} (_h : ¬ CommensurableInSquare x y)
    (hs : MedialArea ρ (sq x + sq y)) (hr : MedialArea ρ (rect x y))
    (hi : ¬ Commensurable (sq x + sq y) (rect x y)) (hl : l + y = x) :
      ¬ Rational ρ l := by
  -- twice the rectangle taken from the squares leaves the square on `l` [Prop. 2.7]: the
  -- remaining breadth is an apotome, and the square on `l` irrational [Props. 10.73,
  -- 10.20]
  have h₁ : ¬ Commensurable (sq x + sq y) ((2 : ℕ+) • rect x y) :=
    fun h' => hi (proposition_12 Area.divisible h' (twice_commensurable _).symm)
  have h₂ := medial_sub_medial hs hr.twice h₁ (sq_add_sq_of_sub hl).symm
  exact fun h' => h₂ h'.sq_rational

end Elements.Book10
