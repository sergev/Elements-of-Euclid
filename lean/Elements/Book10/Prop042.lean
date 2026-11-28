import Elements.Book10.Prop041

namespace Elements.Book10

open Elements.Book5 Elements.Book5.Magnitude

variable {ρ : Length}

/-- If two rational areas, each with a medial area added, make equal sums, the rational
areas are equal: else one exceeds the other by a rational area [Props. 10.15, Def. 10.4],
and so would one medial area exceed the other [Prop. 10.26]. The argument of 10.42, 10.43,
10.45, 10.46, and of 10.79, 10.80, 10.82, 10.83. -/
theorem rational_add_medial_eq {S S' A A' : Area} (hS : RationalArea ρ S)
    (hS' : RationalArea ρ S') (hA : MedialArea ρ A) (hA' : MedialArea ρ A')
    (h : S + A = S' + A') : S = S' := by
  have key : ∀ {S S' A A' : Area}, RationalArea ρ S → RationalArea ρ S' → MedialArea ρ A →
      MedialArea ρ A' → S + A = S' + A' → ¬ S' < S := by
    intro S S' A A' hS hS' hA hA' h hlt
    -- `S` exceeds `S'` by `D`, rational, both being rational
    obtain ⟨D, hD⟩ := remainder _ _ hlt
    have hDr : RationalArea ρ D := hS'.of_comm (proposition_15.2 (hD ▸ hS.comm hS')).symm
    -- so `A'` exceeds `A` by `D`, both being medial: which is impossible [Prop. 10.26]
    have : A + D = A' := add_left_cancel (a := S') (by
      rw [← h, ← hD, add_assoc, add_comm D A, ← add_assoc])
    exact proposition_26 hA' hA this hDr
  rcases lt_trichotomy S' S with hlt | heq | hlt
  · exact absurd hlt (key hS hS' hA hA' h)
  · exact heq.symm
  · exact absurd hlt (key hS' hS hA' hA h.symm)

/-- Terms `x > y` and `x' > y'` with the same sum and the same sum of squares are the
same: else the cuts are unequally far from the middle, and the squares are greater for the
cut further from it [Prop. 10.41 lem.]. -/
theorem eq_of_squares_eq {x y x' y' : Length} (hy : y < x) (hy' : y' < x')
    (he : x + y = x' + y') (hs : sq x + sq y = sq x' + sq y') : x = x' ∧ y = y' := by
  rcases lt_trichotomy x' x with hlt | rfl | hlt
  · exact absurd hs (ne_of_gt (proposition_41_lemma he hlt (hy'.trans hlt)))
  · exact ⟨rfl, add_left_cancel he⟩
  · exact absurd hs (ne_of_lt (proposition_41_lemma he.symm hlt (hy.trans hlt)))

/-- A binomial can be divided into its terms at one point only: two divisions of it into
rational lines commensurable in square only, the greater first, are the same. -/
theorem proposition_42 {x y x' y' : Length} (h : BinomialTerms ρ x y)
    (h' : BinomialTerms ρ x' y') (he : x + y = x' + y') : x = x' ∧ y = y' := by
  obtain ⟨hx, hy, hxy, hyx⟩ := h
  obtain ⟨hx', hy', hxy', hyx'⟩ := h'
  -- the squares and twice the rectangle at each division make the square on the whole
  -- [Prop. 2.4]; the squares are rational, twice the rectangles medial [Prop. 10.21]: so
  -- the squares are equal [Prop. 10.26]
  have h₁ :
      sq x + sq y + (2 : ℕ+) • rect x y = sq x' + sq y' + (2 : ℕ+) • rect x' y' := by
    rw [← sq_add, ← sq_add, he]
  have h₂ := rational_add_medial_eq (hx.sq_rational.of_comm (proposition_15.1 hxy.1).1)
    (hx'.sq_rational.of_comm (proposition_15.1 hxy'.1).1)
    (MedialArea.twice ⟨x, y, hx, hy, hxy, rfl⟩)
      (MedialArea.twice ⟨x', y', hx', hy', hxy', rfl⟩) h₁
  exact eq_of_squares_eq hyx hyx' he h₂

end Elements.Book10
