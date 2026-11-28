import Elements.Book10.Prop033

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- To find two lines incommensurable in square, the sum of the squares on them medial,
the rectangle contained by them rational. -/
theorem proposition_34 : ∃ x y, RationalMedialTerms ρ x y := by
  -- let medial `l`, `a`, commensurable in square only, containing a rational area, be
  -- laid out, the square on `l` exceeding that on `a` by the square on a line
  -- incommensurable with `l` [Prop. 10.31]; and the figure as in 10.33
  obtain ⟨l, a, ⟨hl, ha, hla, hr, hal⟩, he⟩ := proposition_31' (ρ := ρ)
  obtain ⟨h, x, y, u, v, hh, hxy, hr', hu, hv, hsq, hrect⟩ := figure_33 hal
  -- `x` is incommensurable in length with `y` [Prop. 10.18], so the squares on `u`, `v`
  -- [Prop. 10.11]
  have h₁ := figure_33_incomm hu hv ((proposition_18 hal hh hxy hr').mpr he)
  -- the square on `l` is medial, and so the squares on `u`, `v` [Props. 3.31, 1.47]
  have h₂ : MedialArea ρ (sq u + sq v) := hsq ▸ hl
  -- the rectangle contained by `l`, `a` is double that contained by `l`, `h`; it is
  -- rational, and so is that contained by `l`, `h` [Prop. 10.6, Def. 10.4], which is that
  -- contained by `u`, `v` [Prop. 10.32 lem.]
  have h₃ : RationalArea ρ (rect u v) := hrect ▸ hr.of_comm (figure_33_double hh).symm
  refine exists_ordered (P := fun x y => ¬ CommensurableInSquare x y ∧
    MedialArea ρ (sq x + sq y) ∧ RationalArea ρ (rect x y)) ?_ ⟨h₁, h₂, h₃⟩ ?_ |>.imp
    fun x ⟨y, h, hyx⟩ => ⟨y, h.1, h.2.1, h.2.2, hyx⟩
  · rintro x y ⟨h₁, h₂, h₃⟩
    exact ⟨fun h => h₁ h.symm, add_comm (sq x) _ ▸ h₂, rect_comm x y ▸ h₃⟩
  · rintro rfl
    exact h₁ (Commensurable.refl _)

end Elements.Book10
