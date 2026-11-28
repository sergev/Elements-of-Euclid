import Elements.Book10.Prop064

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- The terms of 10.65: the squares on the terms `x > y` of the square root of two medial
areas and twice the rectangle, applied to a rational line `r`, make as breadths the terms
of a sixth binomial. Shared with 10.102. -/
theorem proposition_65_terms {r x y : Length} (hr : Rational ρ r)
    (h : TwoMedialTerms ρ x y) :
    ∃ e d, SixthTerms ρ r e d ∧ rect r e = sq x + sq y ∧
      rect r d = (2 : ℕ+) • rect x y := by
  obtain ⟨hxy, hS, hR, hi, hyx⟩ := h
  obtain ⟨k₁, k₂, h, h₁, h₂, -, hk, hlt, hs, h2⟩ := proposition_60_construction r hyx
  -- the squares and twice the rectangle are medial: `k₁ + k₂` and `h + h` are rational,
  -- incommensurable with `r` [Prop. 10.22]; and with one another, the squares being
  -- incommensurable with twice the rectangle [Props. 10.6, 10.13, 6.1, 10.11]
  obtain ⟨her, heρ⟩ := proposition_22' hS hr hs
  obtain ⟨hdr, hdρ⟩ := proposition_22' hR.twice hr h2
  have hed : ¬ Commensurable (k₁ + k₂) (h + h) := by
    rw [← rect_commensurable_iff r, hs, h2]
    exact fun h' => hi (proposition_12 Area.divisible h' (twice_commensurable _).symm)
  have hk₁₂ : ¬ Commensurable k₁ k₂ := by
    rw [← rect_commensurable_iff r, h₁, h₂]; exact hxy
  exact ⟨k₁ + k₂, h + h, ⟨⟨her, hdr, ⟨her.inSquare_of hdr, hed⟩, hlt⟩,
    (proposition_18 hlt rfl rfl hk).mp hk₁₂, heρ, hdρ⟩, hs, h2⟩

/-- The square on the square root of two medial areas, applied to a rational line `r`,
makes as breadth a sixth binomial. -/
theorem proposition_65 {r l g : Length} (hl : SideTwoMedials ρ l) (hr : Rational ρ r)
    (hg : rect r g = sq l) : SixthBinomial ρ r g := by
  obtain ⟨x, y, h, rfl⟩ := hl
  obtain ⟨e, d, hed, he, hd⟩ := proposition_65_terms hr h
  -- the breadth is `e + d` [Prop. 2.4]
  exact ⟨e, d, hed, breadth_eq_add hg he hd⟩

end Elements.Book10
