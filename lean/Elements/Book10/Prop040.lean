import Elements.Book10.Prop039

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- If two lines incommensurable in square, with the sum of the squares on them medial and
the rectangle contained by them rational, are added together, the whole is irrational:
let it be called the square root of a rational plus a medial area
(`SideRationalMedial`). -/
theorem proposition_40 {x y : Length} (_h : ¬ CommensurableInSquare x y)
    (hs : MedialArea ρ (sq x + sq y)) (hr : RationalArea ρ (rect x y)) :
    ¬ Rational ρ (x + y) := by
  -- the squares, medial, are incommensurable with twice the rectangle, rational; so the
  -- square on the whole with twice the rectangle [Props. 2.4, 10.16], and it is
  -- irrational, and the whole [Def. 10.4]
  have h₁ : ¬ Commensurable (sq x + sq y) ((2 : ℕ+) • rect x y) :=
    fun h' => hs.not_rational (hr.twice.of_comm h')
  have h₂ := (proposition_16.1 h₁).2
  rw [← sq_add] at h₂
  exact fun h' => hr.twice.not_of_not_comm (fun h'' => h₂ h''.symm) h'.sq_rational

end Elements.Book10
