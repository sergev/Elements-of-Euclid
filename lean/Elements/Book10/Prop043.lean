import Elements.Book10.Prop042

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- A first bimedial can be divided into its terms at one point only. -/
theorem proposition_43 {x y x' y' : Length} (h : FirstBimedialTerms ρ x y)
    (h' : FirstBimedialTerms ρ x' y') (he : x + y = x' + y') : x = x' ∧ y = y' := by
  obtain ⟨hx, -, hxy, hr, hyx⟩ := h
  obtain ⟨hx', -, hxy', hr', hyx'⟩ := h'
  -- twice the rectangles are rational, the squares medial [Props. 10.15, 10.23 corr.]:
  -- by whatever twice the one rectangle exceeds the other, so do the squares the other
  -- squares [Props. 2.4, 10.41 lem.], by a rational area; which is impossible [Prop.
  -- 10.26]
  have h₁ : (2 : ℕ+) • rect x y + (sq x + sq y) =
      (2 : ℕ+) • rect x' y' + (sq x' + sq y') := by
    rw [add_comm, ← sq_add, add_comm ((2 : ℕ+) • _), ← sq_add, he]
  have h₂ := rational_add_medial_eq hr.twice hr'.twice
    (proposition_23_corollary hx (proposition_15.1 hxy.1).1)
    (proposition_23_corollary hx' (proposition_15.1 hxy'.1).1) h₁
  have h₃ : sq x + sq y = sq x' + sq y' := add_left_cancel (h₂ ▸ h₁)
  exact eq_of_squares_eq hyx hyx' he h₃

end Elements.Book10
