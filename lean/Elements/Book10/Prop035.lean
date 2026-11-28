import Elements.Book10.Prop034

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- To find two lines incommensurable in square, the sum of the squares on them medial,
the rectangle contained by them medial, and incommensurable with the sum of the
squares. -/
theorem proposition_35 : ∃ x y, TwoMedialTerms ρ x y := by
  -- let medial `l`, `a`, commensurable in square only, containing a medial area, be laid
  -- out, the square on `l` exceeding that on `a` by the square on a line incommensurable
  -- with `l` [Prop. 10.32]; and the figure as before
  obtain ⟨l, a, ⟨hl, ha, hla, hr, hal⟩, he⟩ := proposition_32' (ρ := ρ)
  obtain ⟨h, x, y, u, v, hh, hxy, hr', hu, hv, hsq, hrect⟩ := figure_33 hal
  -- `x` is incommensurable in length with `y` [Prop. 10.18], so `u`, `v` in square [Prop.
  -- 10.11]
  have h₁ := figure_33_incomm hu hv ((proposition_18 hal hh hxy hr').mpr he)
  -- the square on `l` is medial, and so the squares on `u`, `v` [Props. 3.31, 1.47]
  have h₂ : MedialArea ρ (sq u + sq v) := hsq ▸ hl
  -- the rectangle contained by `l`, `a` is medial, so that contained by `l`, `h`, double
  -- it, which is that contained by `u`, `v`
  have h₃ : MedialArea ρ (rect u v) :=
    hrect ▸ proposition_23_corollary hr (figure_33_double hh).symm
  -- `l` is incommensurable in length with `a`, and `a` commensurable with `h`: so `l`
  -- with `h` [Prop. 10.13], and the square on `l` with the rectangle contained by `l`,
  -- `h` [Prop. 10.11]; that is, the squares on `u`, `v` with the rectangle contained by
  -- them
  have h₄ : ¬ Commensurable l h :=
    proposition_13 Length.divisible (hh ▸ double_commensurable h)
      (fun h' => hla.2 h'.symm)
      |> fun h' h'' => h' h''.symm
  have h₅ := (proposition_11 (proposition_21_lemma l h).1 Length.divisible
    Area.divisible).2 h₄
  rw [← hsq, hrect] at h₅
  refine exists_ordered (P := fun x y => ¬ CommensurableInSquare x y ∧
    MedialArea ρ (sq x + sq y) ∧ MedialArea ρ (rect x y) ∧
      ¬ Commensurable (sq x + sq y) (rect x y)) ?_ ⟨h₁, h₂, h₃, h₅⟩ ?_ |>.imp
    fun x ⟨y, h, hyx⟩ => ⟨y, h.1, h.2.1, h.2.2.1, h.2.2.2, hyx⟩
  · rintro x y ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨fun h => h₁ h.symm, add_comm (sq x) _ ▸ h₂, rect_comm x y ▸ h₃,
      add_comm (sq x) (sq y) ▸ rect_comm x y ▸ h₄⟩
  · rintro rfl
    exact h₁ (Commensurable.refl _)

end Elements.Book10
