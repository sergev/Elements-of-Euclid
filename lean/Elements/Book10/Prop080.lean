import Elements.Book10.Prop079

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- Only one medial line, commensurable in square only with the whole and containing a
rational area with it, can be attached to a first apotome of a medial. The mirror of
10.43. -/
theorem proposition_80 {l x y x' y' : Length} (h : FirstBimedialTerms ρ x y)
    (h' : FirstBimedialTerms ρ x' y') (hl : l + y = x) (hl' : l + y' = x') :
    x = x' ∧ y = y' := by
  obtain ⟨hx, -, hxy, hr, -⟩ := h
  obtain ⟨hx', -, hxy', hr', -⟩ := h'
  -- by whatever twice the one rectangle exceeds the other, the squares exceed the other
  -- squares [Prop. 2.7], by a rational area, both being medial [Prop. 10.26]
  have h₁ := squares_sub_eq hl hl'
  have h₁' : (2 : ℕ+) • rect x y + (sq x' + sq y') =
      (2 : ℕ+) • rect x' y' + (sq x + sq y) := by
    rw [add_comm, ← h₁, add_comm]
  have h₂ := rational_add_medial_eq hr.twice hr'.twice
    (proposition_23_corollary hx' (proposition_15.1 hxy'.1).1)
    (proposition_23_corollary hx (proposition_15.1 hxy.1).1) h₁'
  rw [h₂] at h₁'
  exact eq_of_squares_eq_sub hl hl' (add_left_cancel h₁').symm

end Elements.Book10
