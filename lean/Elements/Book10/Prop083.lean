import Elements.Book10.Prop082

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- Only one line, incommensurable in square with the whole and making with it the squares
medial and twice the rectangle rational, can be attached to that which makes with a
rational area a medial whole. The mirror of 10.46. -/
theorem proposition_83 {l x y x' y' : Length} (h : RationalMedialTerms ρ x y)
    (h' : RationalMedialTerms ρ x' y') (hl : l + y = x) (hl' : l + y' = x') :
    x = x' ∧ y = y' := by
  obtain ⟨-, hs, hr, -⟩ := h
  obtain ⟨-, hs', hr', -⟩ := h'
  have h₁ := squares_sub_eq hl hl'
  have h₁' : (2 : ℕ+) • rect x y + (sq x' + sq y') =
      (2 : ℕ+) • rect x' y' + (sq x + sq y) := by
    rw [add_comm, ← h₁, add_comm]
  have h₂ := rational_add_medial_eq hr.twice hr'.twice hs' hs h₁'
  rw [h₂] at h₁'
  exact eq_of_squares_eq_sub hl hl' (add_left_cancel h₁').symm

end Elements.Book10
