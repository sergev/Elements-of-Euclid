import Elements.Book10.Prop081

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- Only one line, incommensurable in square with the whole and making with it the squares
rational and twice the rectangle medial, can be attached to a minor line. The mirror of
10.45 (Fitzpatrick: 10.45 with minus signs). -/
theorem proposition_82 {l x y x' y' : Length} (h : MajorTerms ρ x y)
    (h' : MajorTerms ρ x' y')
    (hl : l + y = x) (hl' : l + y' = x') : x = x' ∧ y = y' := by
  obtain ⟨-, hs, hr, -⟩ := h
  obtain ⟨-, hs', hr', -⟩ := h'
  exact eq_of_squares_eq_sub hl hl'
    (rational_add_medial_eq hs hs' hr'.twice hr.twice (squares_sub_eq hl hl'))

end Elements.Book10
