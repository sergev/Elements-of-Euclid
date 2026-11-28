import Elements.Book10.Prop019

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- If a rational area is applied to a rational line `r`, the breadth `x` is rational,
and commensurable in length with `r`. -/
theorem proposition_20 {r x : Length} {A : Area} (hr : Rational ρ r) (hA : RationalArea ρ
    A)
    (h : rect r x = A) : Rational ρ x ∧ Commensurable x r := by
  -- the square on `r` is rational [Def. 10.4], so commensurable with `A`; and as the
  -- square on `r` is to `A`, so `r` to `x` [Prop. 6.1]: they are commensurable [Prop.
  -- 10.11]
  have h₁ : Proportion (sq r) A r x := h ▸ rect_proportion' r x r
  have h₂ := (proposition_11 h₁ Area.divisible Length.divisible).1
    (hr.sq_rational.comm hA)
  -- `r` is rational: so `x` is rational [Def. 10.3]
  exact ⟨hr.of_comm h₂.symm, h₂.symm⟩

end Elements.Book10
