import Elements.Book10.Prop078

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- Two lines `y`, `y'` attached to the same `l`, making `x`, `x'`, with the same sum of
squares, are the same: the greater attached line makes the greater whole, and the greater
squares. -/
theorem eq_of_squares_eq_sub {l x y x' y' : Length} (hl : l + y = x) (hl' : l + y' = x')
    (hs : sq x + sq y = sq x' + sq y') : x = x' ∧ y = y' := by
  have key : ∀ {x y x' y' : Length}, l + y = x → l + y' = x' → y < y' →
      sq x + sq y < sq x' + sq y' := by
    intro x y x' y' hl hl' hlt
    subst hl hl'
    exact add_lt_add (sq_lt_sq.mpr (add_lt_add_right hlt l)) (sq_lt_sq.mpr hlt)
  rcases lt_trichotomy y y' with hlt | rfl | hlt
  · exact absurd hs (ne_of_lt (key hl hl' hlt))
  · exact ⟨hl.symm.trans hl', rfl⟩
  · exact absurd hs (ne_of_gt (key hl' hl hlt))

/-- In a difference, the squares on the terms with twice the other rectangle equal the
other squares with twice the rectangle: both squares exceed twice their rectangle by the
square on the difference [Prop. 2.7]. -/
theorem squares_sub_eq {l x y x' y' : Length} (hl : l + y = x) (hl' : l + y' = x') :
    sq x + sq y + (2 : ℕ+) • rect x' y' = sq x' + sq y' + (2 : ℕ+) • rect x y := by
  rw [sq_add_sq_of_sub hl, sq_add_sq_of_sub hl']
  ac_rfl

/-- Only one rational line, commensurable in square only with the whole, can be attached
to an apotome: if `y` and `y'` are so attached to `l`, they are the same. -/
theorem proposition_79 {l x y x' y' : Length} (h : BinomialTerms ρ x y)
    (h' : BinomialTerms ρ x' y') (hl : l + y = x) (hl' : l + y' = x') : x =
      x' ∧ y = y' := by
  obtain ⟨hx, hy, hxy, -⟩ := h
  obtain ⟨hx', hy', hxy', -⟩ := h'
  -- by whatever the squares exceed the other squares, twice the one rectangle exceeds the
  -- other [Prop. 2.7], by a rational area, both being medial: impossible [Prop. 10.26]
  have h₂ := rational_add_medial_eq (hx.sq_rational.of_comm (proposition_15.1 hxy.1).1)
    (hx'.sq_rational.of_comm (proposition_15.1 hxy'.1).1)
    (MedialArea.twice ⟨x', y', hx', hy', hxy', rfl⟩)
    (MedialArea.twice ⟨x, y, hx, hy, hxy, rfl⟩) (squares_sub_eq hl hl')
  exact eq_of_squares_eq_sub hl hl' h₂

end Elements.Book10
