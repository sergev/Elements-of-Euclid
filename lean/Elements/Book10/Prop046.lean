import Elements.Book10.Prop045

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- The square root of a rational plus a medial area can be divided into its terms at one
point only. -/
theorem proposition_46 {x y x' y' : Length} (h : RationalMedialTerms ρ x y)
    (h' : RationalMedialTerms ρ x' y') (he : x + y = x' + y') : x = x' ∧ y = y' := by
  obtain ⟨-, hs, hr, hyx⟩ := h
  obtain ⟨-, hs', hr', hyx'⟩ := h'
  -- twice the rectangles are rational, the squares medial: by whatever twice the one
  -- rectangle exceeds the other, the other squares exceed the squares [Prop. 2.4], by a
  -- rational area; which is impossible [Prop. 10.26]
  have h₁ : (2 : ℕ+) • rect x y + (sq x + sq y) =
      (2 : ℕ+) • rect x' y' + (sq x' + sq y') := by
    rw [add_comm, ← sq_add, add_comm ((2 : ℕ+) • _), ← sq_add, he]
  have h₂ := rational_add_medial_eq hr.twice hr'.twice hs hs' h₁
  exact eq_of_squares_eq hyx hyx' he (add_left_cancel (h₂ ▸ h₁))

end Elements.Book10
