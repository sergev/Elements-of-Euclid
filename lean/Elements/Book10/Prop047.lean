import Elements.Book10.Prop046

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- The square root of two medial areas can be divided into its terms at one point
only. -/
theorem proposition_47 {x y x' y' : Length} (h : TwoMedialTerms ρ x y)
    (h' : TwoMedialTerms ρ x' y') (he : x + y = x' + y') : x = x' ∧ y = y' := by
  obtain ⟨-, hs, hr, hi, hyx⟩ := h
  obtain ⟨-, hs', hr', hi', hyx'⟩ := h'
  -- the squares and twice the rectangles are medial, and incommensurable [Prop. 10.6,
  -- 10.13]: applied to a rational line, each pair makes a binomial as breadth, divided at
  -- two points; which is impossible [Prop. 10.42]
  have h₁ :
      sq x + sq y + (2 : ℕ+) • rect x y = sq x' + sq y' + (2 : ℕ+) • rect x' y' := by
    rw [← sq_add, ← sq_add, he]
  have hi₂ : ∀ {x y : Length}, ¬ Commensurable (sq x + sq y) (rect x y) →
      ¬ Commensurable (sq x + sq y) ((2 : ℕ+) • rect x y) :=
    fun hi h' => hi (proposition_12 Area.divisible h' (twice_commensurable _).symm)
  have h₂ := medial_add_medial_eq hs hs' hr.twice hr'.twice (hi₂ hi) (hi₂ hi')
    (twice_rect_lt_squares hyx) (twice_rect_lt_squares hyx') h₁
  exact eq_of_squares_eq hyx hyx' he h₂

end Elements.Book10
