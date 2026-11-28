import Elements.Book10.Prop063

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- The square on the square root of a rational plus a medial area, applied to a rational
line `r`, makes as breadth a fifth binomial. -/
theorem proposition_64 {r l g : Length} (hl : SideRationalMedial ρ l) (hr : Rational ρ r)
    (hg : rect r g = sq l) : FifthBinomial ρ r g := by
  obtain ⟨x, y, ⟨hxy, hS, hR, hyx⟩, rfl⟩ := hl
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
    (proposition_18 hlt rfl rfl hk).mp hk₁₂, hdρ⟩, breadth_eq_add hg hs h2⟩

end Elements.Book10
