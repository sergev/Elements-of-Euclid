import Elements.Book10.Prop038

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- If two lines incommensurable in square, with the sum of the squares on them rational
and the rectangle contained by them medial, are added together, the whole is irrational:
let it be called a major line (`Major`). -/
theorem proposition_39 {x y : Length} (_h : ¬ CommensurableInSquare x y)
    (hs : RationalArea ρ (sq x + sq y)) (hr : MedialArea ρ (rect x y)) :
    ¬ Rational ρ (x + y) := by
  -- twice the rectangle is medial [Props. 10.6, 10.23 corr.], so incommensurable with the
  -- squares, rational [Def. 10.4]; so the square on the whole with the squares [Props.
  -- 2.4, 10.16], and it is irrational, and the whole [Def. 10.4]
  have h₁ : ¬ Commensurable (sq x + sq y) ((2 : ℕ+) • rect x y) :=
    fun h' => hr.twice.not_rational (hs.of_comm h'.symm)
  have h₂ := (proposition_16.1 h₁).1
  rw [← sq_add] at h₂
  exact fun h' => hs.not_of_not_comm (fun h'' => h₂ h''.symm) h'.sq_rational

end Elements.Book10
