import Elements.Book10.Prop062

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- The terms of 10.63: the squares on the terms `x > y` of a major line and twice the
rectangle, applied to a rational line `r`, make as breadths the terms of a fourth
binomial. Shared with 10.100. -/
theorem proposition_63_terms {r x y : Length} (hr : Rational ρ r) (h : MajorTerms ρ x y) :
    ∃ e d, FourthTerms ρ r e d ∧ rect r e = sq x + sq y ∧
      rect r d = (2 : ℕ+) • rect x y := by
  obtain ⟨hxy, hS, hR, hyx⟩ := h
  obtain ⟨k₁, k₂, h, h₁, h₂, -, hk, hlt, hs, h2⟩ := proposition_60_construction r hyx
  -- the squares are rational: `k₁ + k₂` is rational, commensurable with `r` [Prop.
  -- 10.20]; twice the rectangle is medial: `h + h` is rational, incommensurable with `r`
  -- [Prop. 10.22]; so they are incommensurable [Prop. 10.13]
  obtain ⟨her, heρ⟩ := proposition_20 hr hS hs
  obtain ⟨hdr, hdρ⟩ := proposition_22' hR.twice hr h2
  have hed : ¬ Commensurable (k₁ + k₂) (h + h) :=
    fun h' => hdρ (proposition_12 Length.divisible h'.symm heρ.symm)
  -- `k₁`, `k₂` are incommensurable, as the squares [Props. 6.1, 10.11]: the square on
  -- `k₁ + k₂` exceeds that on `h + h` by the square on a line incommensurable with it
  -- [Prop. 10.18]
  have hk₁₂ : ¬ Commensurable k₁ k₂ := by
    rw [← rect_commensurable_iff r, h₁, h₂]; exact hxy
  exact ⟨k₁ + k₂, h + h, ⟨⟨her, hdr, ⟨her.inSquare_of hdr, hed⟩, hlt⟩,
    (proposition_18 hlt rfl rfl hk).mp hk₁₂, heρ⟩, hs, h2⟩

/-- The square on a major line, applied to a rational line `r`, makes as breadth a fourth
binomial. -/
theorem proposition_63 {r l g : Length} (hl : Major ρ l) (hr : Rational ρ r)
    (hg : rect r g = sq l) : FourthBinomial ρ r g := by
  obtain ⟨x, y, h, rfl⟩ := hl
  obtain ⟨e, d, hed, he, hd⟩ := proposition_63_terms hr h
  -- the breadth is `e + d` [Prop. 2.4]
  exact ⟨e, d, hed, breadth_eq_add hg he hd⟩

end Elements.Book10
