import Elements.Book10.Prop060

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- The terms of 10.61: the squares on the terms `x > y` of a first bimedial and twice the
rectangle, applied to a rational line `r`, make as breadths the terms of a second
binomial. Shared with 10.98. -/
theorem proposition_61_terms {r x y : Length} (hr : Rational ρ r)
    (h : FirstBimedialTerms ρ x y) :
    ∃ e d, SecondTerms ρ r e d ∧ rect r e = sq x + sq y ∧
      rect r d = (2 : ℕ+) • rect x y := by
  obtain ⟨hx, -, hxy, hR, hyx⟩ := h
  -- the same construction as in 10.60
  obtain ⟨k₁, k₂, h, h₁, h₂, -, hk, hlt, hs, h2⟩ := proposition_60_construction r hyx
  -- the squares are medial [Props. 10.15, 10.23 corr.]: `k₁ + k₂` is rational,
  -- incommensurable in length with `r` [Prop. 10.22]
  obtain ⟨her, heρ⟩ :=
    proposition_22' (proposition_23_corollary hx (proposition_15.1 hxy.1).1) hr hs
  -- twice the rectangle is rational: `h + h` is rational, commensurable with `r` [Prop.
  -- 10.20]
  obtain ⟨hdr, hdρ⟩ := proposition_20 hr hR.twice h2
  -- so they are incommensurable in length [Prop. 10.13]
  have hed : ¬ Commensurable (k₁ + k₂) (h + h) :=
    fun h' => heρ (proposition_12 Length.divisible h' hdρ.symm)
  -- `k₁`, `k₂` are commensurable [Props. 6.1, 10.11]: the square on `k₁ + k₂` exceeds
  -- that on `h + h` by the square on a line commensurable with it [Prop. 10.17]
  have hk₁₂ : Commensurable k₁ k₂ := (rect_commensurable_iff r).mp
    (by rw [h₁, h₂]; exact hxy.1)
  exact ⟨k₁ + k₂, h + h, ⟨⟨her, hdr, ⟨her.inSquare_of hdr, hed⟩, hlt⟩,
    (proposition_17 hlt rfl rfl hk).mp hk₁₂, hdρ⟩, hs, h2⟩

/-- The square on a first bimedial, applied to a rational line `r`, makes as breadth a
second binomial. -/
theorem proposition_61 {r l g : Length} (hl : FirstBimedial ρ l) (hr : Rational ρ r)
    (hg : rect r g = sq l) : SecondBinomial ρ r g := by
  obtain ⟨x, y, h, rfl⟩ := hl
  obtain ⟨e, d, hed, he, hd⟩ := proposition_61_terms hr h
  -- the breadth is `e + d` [Prop. 2.4]
  exact ⟨e, d, hed, breadth_eq_add hg he hd⟩

end Elements.Book10
