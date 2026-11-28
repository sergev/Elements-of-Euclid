import Elements.Book10.Prop063

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- The terms of 10.64: the squares on the terms `x > y` of the square root of a rational
plus a medial area and twice the rectangle, applied to a rational line `r`, make as
breadths the terms of a fifth binomial. Shared with 10.101. -/
theorem proposition_64_terms {r x y : Length} (hr : Rational ρ r)
    (h : RationalMedialTerms ρ x y) :
    ∃ e d, FifthTerms ρ r e d ∧ rect r e = sq x + sq y ∧
      rect r d = (2 : ℕ+) • rect x y := by
  obtain ⟨hxy, hS, hR, hyx⟩ := h
  obtain ⟨k₁, k₂, h, h₁, h₂, -, hk, hlt, hs, h2⟩ := proposition_60_construction r hyx
  -- the squares are medial: `k₁ + k₂` is rational, incommensurable with `r` [Prop.
  -- 10.22]; twice the rectangle is rational: `h + h` is rational, commensurable with `r`
  -- [Prop. 10.20]; so they are incommensurable [Prop. 10.13]
  obtain ⟨her, heρ⟩ := proposition_22' hS hr hs
  obtain ⟨hdr, hdρ⟩ := proposition_20 hr hR.twice h2
  have hed : ¬ Commensurable (k₁ + k₂) (h + h) :=
    fun h' => heρ (proposition_12 Length.divisible h' hdρ.symm)
  have hk₁₂ : ¬ Commensurable k₁ k₂ := by
    rw [← rect_commensurable_iff r, h₁, h₂]; exact hxy
  exact ⟨k₁ + k₂, h + h, ⟨⟨her, hdr, ⟨her.inSquare_of hdr, hed⟩, hlt⟩,
    (proposition_18 hlt rfl rfl hk).mp hk₁₂, hdρ⟩, hs, h2⟩

/-- The square on the square root of a rational plus a medial area, applied to a rational
line `r`, makes as breadth a fifth binomial. -/
theorem proposition_64 {r l g : Length} (hl : SideRationalMedial ρ l) (hr : Rational ρ r)
    (hg : rect r g = sq l) : FifthBinomial ρ r g := by
  obtain ⟨x, y, h, rfl⟩ := hl
  obtain ⟨e, d, hed, he, hd⟩ := proposition_64_terms hr h
  -- the breadth is `e + d` [Prop. 2.4]
  exact ⟨e, d, hed, breadth_eq_add hg he hd⟩

end Elements.Book10
