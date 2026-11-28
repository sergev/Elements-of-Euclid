import Elements.Book10.Prop062

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- The square on a major line, applied to a rational line `r`, makes as breadth a fourth
binomial. -/
theorem proposition_63 {r l g : Length} (hl : Major ρ l) (hr : Rational ρ r)
    (hg : rect r g = sq l) : FourthBinomial ρ r g := by
  obtain ⟨x, y, ⟨hxy, hS, hR, hyx⟩, rfl⟩ := hl
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
    (proposition_18 hlt rfl rfl hk).mp hk₁₂, heρ⟩, breadth_eq_add hg hs h2⟩

end Elements.Book10
