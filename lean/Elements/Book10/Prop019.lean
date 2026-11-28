import Elements.Book10.Prop018

namespace Elements.Book10

open Elements.Book5 Elements.Book5.Magnitude

variable {ρ : Length}

/-! Rational lines and areas: Defs. 10.3 and 10.4, with 10.9's corollary, 10.12 and
10.13, as Euclid uses them from here on. -/

/-- A rational line is commensurable in square with `ρ` [Prop. 10.9 corr.]. -/
theorem Rational.inSquare {x : Length} (hx : Rational ρ x) : CommensurableInSquare x ρ :=
  hx.elim proposition_9_corollary id

/-- The square on a rational line is rational [Def. 10.4]. -/
theorem Rational.sq_rational {x : Length} (hx : Rational ρ x) : RationalArea ρ (sq x) :=
  hx.inSquare

/-- A line on which the square is rational is rational [Def. 10.3]. -/
theorem Rational.of_sq {x : Length} (h : RationalArea ρ (sq x)) : Rational ρ x := Or.inr h

/-- Rational areas are commensurable [Prop. 10.12]. -/
theorem RationalArea.comm {A B : Area} (hA : RationalArea ρ A) (hB : RationalArea ρ B) :
    Commensurable A B :=
  proposition_12 Area.divisible hA hB

/-- An area commensurable with a rational area is rational [Def. 10.4, Prop. 10.12]. -/
theorem RationalArea.of_comm {A B : Area} (hA : RationalArea ρ A) (h : Commensurable B A)
    :
    RationalArea ρ B :=
  proposition_12 Area.divisible h hA.symm

/-- An area incommensurable with a rational area is irrational [Def. 10.4]. -/
theorem RationalArea.not_of_not_comm {A B : Area} (hA : RationalArea ρ A)
    (h : ¬ Commensurable A B) : ¬ RationalArea ρ B :=
  fun hB => h (hA.comm hB)

/-- Rational lines are commensurable in square [Prop. 10.12]. -/
theorem Rational.inSquare_of {x y : Length} (hx : Rational ρ x) (hy : Rational ρ y) :
    CommensurableInSquare x y :=
  hx.sq_rational.comm hy.sq_rational

/-- A line commensurable in length with a rational line is rational [Def. 10.3, Props.
10.9 corr., 10.12]. -/
theorem Rational.of_comm {x y : Length} (hx : Rational ρ x) (h : Commensurable y x) :
    Rational ρ y :=
  hx.elim (fun hxρ => Or.inl (proposition_12 Length.divisible h hxρ.symm))
    (fun hxρ => Or.inr (proposition_12 Area.divisible (proposition_9_corollary h)
      hxρ.symm))

/-- A line commensurable in square with a rational line is rational [Def. 10.3, Prop.
10.12]. -/
theorem Rational.of_inSquare {x y : Length} (hx : Rational ρ x)
    (h : CommensurableInSquare y x) : Rational ρ y :=
  Or.inr (proposition_12 Area.divisible h hx.sq_rational.symm)

/-- The rectangle contained by rational lines commensurable in length is rational. -/
theorem proposition_19 {x y : Length} (hx : Rational ρ x) (_hy : Rational ρ y)
    (h : Commensurable x y) : RationalArea ρ (rect x y) := by
  -- the square on `x` is rational [Def. 10.4]; as `x` is to `y`, so the square on `x` to
  -- the rectangle contained by `x` and `y` [Prop. 6.1]: they are commensurable [Prop.
  -- 10.11]
  have h₁ : Proportion (sq x) (rect y x) x y := rect_proportion x y x
  rw [rect_comm] at h₁
  have h₂ := (proposition_11 h₁.symm Length.divisible Area.divisible).1 h
  exact hx.sq_rational.of_comm h₂.symm

end Elements.Book10
