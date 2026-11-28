import Elements.Book10.Prop064

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- The square on the square root of two medial areas, applied to a rational line `r`,
makes as breadth a sixth binomial. -/
theorem proposition_65 {r l g : Length} (hl : SideTwoMedials ρ l) (hr : Rational ρ r)
    (hg : rect r g = sq l) : SixthBinomial ρ r g := by
  obtain ⟨x, y, ⟨hxy, hS, hR, hi, hyx⟩, rfl⟩ := hl
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
    (proposition_18 hlt rfl rfl hk).mp hk₁₂, heρ, hdρ⟩, breadth_eq_add hg hs h2⟩

end Elements.Book10
