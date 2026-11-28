import Elements.Book10.Prop035

namespace Elements.Book10

open Elements.Book5 Elements.Book5.Magnitude

variable {ρ : Length}

/-- Twice a magnitude is commensurable with it [Prop. 10.6]. -/
theorem twice_commensurable {M : Type*} [Magnitude M] (a : M) :
    Commensurable ((2 : ℕ+) • a) a := by
  rw [show (2 : ℕ+) = 1 + 1 from rfl, mult_succ, one_mult]
  exact double_commensurable a

/-- A medial area is irrational [Prop. 10.21]. -/
theorem MedialArea.not_rational {A : Area} (h : MedialArea ρ A) : ¬ RationalArea ρ A := by
  obtain ⟨x, y, hx, hy, hxy, rfl⟩ := h
  exact (proposition_21 hx hy hxy).1

/-- Twice a medial area is medial [Props. 10.6, 10.23 corr.]. -/
theorem MedialArea.twice {A : Area} (h : MedialArea ρ A) : MedialArea ρ ((2 : ℕ+) • A) :=
  proposition_23_corollary h (twice_commensurable A)

/-- Twice a rational area is rational [Prop. 10.6, Def. 10.4]. -/
theorem RationalArea.twice {A : Area} (h : RationalArea ρ A) :
    RationalArea ρ ((2 : ℕ+) • A) :=
  h.of_comm (twice_commensurable A)

/-- For lines commensurable in square only, the sum of the squares on them is
incommensurable with twice the rectangle contained by them: as `x` is to `y`, so the
rectangle to the square on `y` [Prop. 10.21 lem.], so they are incommensurable [Prop.
10.11]; twice the rectangle is commensurable with the rectangle [Prop. 10.6], and the sum
of the squares with the square on `y` [Prop. 10.15] [Prop. 10.13]. 10.36's argument, and
10.37's, 10.38's, 10.73's, 10.74's and 10.75's. -/
theorem InSquareOnly.squares_twice_rect {x y : Length} (h : InSquareOnly x y) :
    ¬ Commensurable (sq x + sq y) ((2 : ℕ+) • rect x y) := by
  have h₁ := (proposition_11 (proposition_21_lemma y x).2.symm Length.divisible
    Area.divisible).2 h.2
  have h₂ := proposition_13 Area.divisible (proposition_15.1 h.1).2.symm
    (fun h' => h₁ h'.symm)
  exact fun h' => proposition_13 Area.divisible (twice_commensurable (rect x y)).symm
    (fun h'' => h₂ h''.symm) h'.symm

/-- If two rational lines commensurable in square only are added together, the whole is
irrational: let it be called a binomial (`Binomial`). -/
theorem proposition_36 {x y : Length} (hx : Rational ρ x) (_hy : Rational ρ y)
    (h : InSquareOnly x y) : ¬ Rational ρ (x + y) := by
  -- twice the rectangle is incommensurable with the squares, so the square on the whole,
  -- the squares and twice the rectangle [Prop. 2.4], with the squares [Prop. 10.16]
  have h₁ := (proposition_16.1 h.squares_twice_rect).1
  rw [← sq_add] at h₁
  -- the squares are rational: so the square on the whole is irrational, and the whole
  -- [Def. 10.4]
  have h₂ := (hx.sq_rational.of_comm (proposition_15.1 h.1).1).not_of_not_comm
    (fun h' => h₁ h'.symm)
  exact fun h' => h₂ h'.sq_rational

end Elements.Book10
