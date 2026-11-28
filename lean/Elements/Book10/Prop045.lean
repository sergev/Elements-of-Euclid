import Elements.Book10.Prop044

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- A major line can be divided into its terms at one point only. -/
theorem proposition_45 {x y x' y' : Length} (h : MajorTerms ρ x y)
    (h' : MajorTerms ρ x' y') (he : x + y = x' + y') : x = x' ∧ y = y' := by
  obtain ⟨-, hs, hr, hyx⟩ := h
  obtain ⟨-, hs', hr', hyx'⟩ := h'
  -- the squares are rational, twice the rectangles medial: by whatever the squares exceed
  -- the other squares, twice the one rectangle exceeds the other [Prop. 2.4], by a
  -- rational area; which is impossible [Prop. 10.26]
  have h₁ :
      sq x + sq y + (2 : ℕ+) • rect x y = sq x' + sq y' + (2 : ℕ+) • rect x' y' := by
    rw [← sq_add, ← sq_add, he]
  exact eq_of_squares_eq hyx hyx' he (rational_add_medial_eq hs hs' hr.twice hr'.twice h₁)

end Elements.Book10
