import Elements.Book10.Prop083

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- Only one line, incommensurable in square with the whole and making with it the squares
medial, twice the rectangle medial and incommensurable with the squares, can be attached
to that which makes with a medial area a medial whole. The mirror of 10.47. -/
theorem proposition_84 {l x y x' y' : Length} (h : TwoMedialTerms ρ x y)
    (h' : TwoMedialTerms ρ x' y') (hl : l + y = x) (hl' : l + y' = x') :
    x = x' ∧ y = y' := by
  obtain ⟨-, hs, hr, hi, hyx⟩ := h
  obtain ⟨-, hs', hr', hi', hyx'⟩ := h'
  have hi₂ : ∀ {x y : Length}, ¬ Commensurable (sq x + sq y) (rect x y) →
      ¬ Commensurable (sq x + sq y) ((2 : ℕ+) • rect x y) :=
    fun hi h' => hi (proposition_12 Area.divisible h' (twice_commensurable _).symm)
  have h₂ := medial_sub_medial_eq hs hs' hr.twice hr'.twice (hi₂ hi) (hi₂ hi')
    (twice_rect_lt_squares hyx) (twice_rect_lt_squares hyx') (squares_sub_eq hl hl')
  exact eq_of_squares_eq_sub hl hl' h₂

end Elements.Book10
