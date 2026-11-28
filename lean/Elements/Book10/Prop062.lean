import Elements.Book10.Prop061

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- The terms of 10.62: the squares on the terms `x > y` of a second bimedial and twice
the rectangle, applied to a rational line `r`, make as breadths the terms of a third
binomial. Shared with 10.99. -/
theorem proposition_62_terms {r x y : Length} (hr : Rational ρ r)
    (h : SecondBimedialTerms ρ x y) :
    ∃ e d, ThirdTerms ρ r e d ∧ rect r e = sq x + sq y ∧
      rect r d = (2 : ℕ+) • rect x y := by
  obtain ⟨hx, -, hxy, hR, hyx⟩ := h
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
    (proposition_17 hlt rfl rfl hk).mp hk₁₂, heρ, hdρ⟩, hs, h2⟩

/-- The square on a second bimedial, applied to a rational line `r`, makes as breadth a
third binomial. -/
theorem proposition_62 {r l g : Length} (hl : SecondBimedial ρ l) (hr : Rational ρ r)
    (hg : rect r g = sq l) : ThirdBinomial ρ r g := by
  obtain ⟨x, y, h, rfl⟩ := hl
  obtain ⟨e, d, hed, he, hd⟩ := proposition_62_terms hr h
  -- the breadth is `e + d` [Prop. 2.4]
  exact ⟨e, d, hed, breadth_eq_add hg he hd⟩

end Elements.Book10
