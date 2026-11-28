import Elements.Book10.Prop072

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- If `x` is cut into `l` and `y`, and the squares on `x`, `y` are incommensurable with
twice the rectangle, they are incommensurable with the square on `l`: they are twice the
rectangle and the square on `l` [Prop. 2.7] [Props. 10.13, 10.16]. 10.73's and 10.76's
step. -/
theorem squares_incomm_sq_sub {l x y : Length} (hl : l + y = x)
    (h : ¬ Commensurable (sq x + sq y) ((2 : ℕ+) • rect x y)) :
    ¬ Commensurable (sq x + sq y) (sq l) := by
  rw [sq_add_sq_of_sub hl] at h ⊢
  exact (proposition_16.1 (proposition_16.2 h)).2

/-- And twice the rectangle is incommensurable with the square on `l` [Props. 2.7, 10.16].
10.74's and 10.77's step. -/
theorem twice_rect_incomm_sq_sub {l x y : Length} (hl : l + y = x)
    (h : ¬ Commensurable (sq x + sq y) ((2 : ℕ+) • rect x y)) :
    ¬ Commensurable ((2 : ℕ+) • rect x y) (sq l) := by
  rw [sq_add_sq_of_sub hl] at h
  exact proposition_16.2 h

/-- If a rational line `y`, commensurable in square only with the whole `x`, is taken from
it, the remainder `l` is irrational: let it be called an apotome (`Apotome`). The same as
10.36, with 2.7 for 2.4. -/
theorem proposition_73 {l x y : Length} (hx : Rational ρ x) (_hy : Rational ρ y)
    (h : InSquareOnly x y) (hl : l + y = x) : ¬ Rational ρ l := by
  -- the squares are incommensurable with twice the rectangle [Prop. 10.36], so with the
  -- remaining square on `l` [Props. 2.7, 10.13, 10.16]; they are rational, so the square
  -- on `l` is irrational, and `l` [Def. 10.4]
  have h₁ := squares_incomm_sq_sub hl h.squares_twice_rect
  exact fun h' => (hx.sq_rational.of_comm (proposition_15.1 h.1).1).not_of_not_comm h₁
    h'.sq_rational

end Elements.Book10
