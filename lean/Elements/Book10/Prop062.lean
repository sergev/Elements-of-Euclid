import Elements.Book10.Prop061

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- The square on a second bimedial, applied to a rational line `r`, makes as breadth a
third binomial. -/
theorem proposition_62 {r l g : Length} (hl : SecondBimedial ρ l) (hr : Rational ρ r)
    (hg : rect r g = sq l) : ThirdBinomial ρ r g := by
  obtain ⟨x, y, ⟨hx, -, hxy, hR, hyx⟩, rfl⟩ := hl
  obtain ⟨k₁, k₂, h, h₁, h₂, -, hk, hlt, hs, h2⟩ := proposition_60_construction r hyx
  -- the squares and twice the rectangle are medial: `k₁ + k₂` and `h + h` are rational,
  -- incommensurable in length with `r` [Prop. 10.22]
  obtain ⟨her, heρ⟩ :=
    proposition_22' (proposition_23_corollary hx (proposition_15.1 hxy.1).1) hr hs
  obtain ⟨hdr, hdρ⟩ := proposition_22' hR.twice hr h2
  -- the squares are incommensurable with twice the rectangle [Prop. 10.36], so the
  -- breadths [Props. 6.1, 10.11]
  have hed : ¬ Commensurable (k₁ + k₂) (h + h) := by
    rw [← rect_commensurable_iff r, hs, h2]; exact hxy.squares_twice_rect
  have hk₁₂ : Commensurable k₁ k₂ := (rect_commensurable_iff r).mp
    (by rw [h₁, h₂]; exact hxy.1)
  exact ⟨k₁ + k₂, h + h, ⟨⟨her, hdr, ⟨her.inSquare_of hdr, hed⟩, hlt⟩,
    (proposition_17 hlt rfl rfl hk).mp hk₁₂, heρ, hdρ⟩, breadth_eq_add hg hs h2⟩

end Elements.Book10
