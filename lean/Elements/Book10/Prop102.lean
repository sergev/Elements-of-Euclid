import Elements.Book10.Prop101

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- The square on that which with a medial area makes a medial whole, applied to a
rational line `r`, makes as breadth a sixth apotome. The same construction as 10.65, the
breadth of twice the rectangle taken from that of the squares. -/
theorem proposition_102 {r l g : Length} (hl : MedialWholeWithMedial ρ l)
    (hr : Rational ρ r) (hg : rect r g = sq l) : SixthApotome ρ r g := by
  obtain ⟨x, y, h, hl⟩ := hl
  obtain ⟨e, d, hed, he, hd⟩ := proposition_65_terms hr h
  -- the breadth is `e - d` [Prop. 2.7]
  exact ⟨e, d, hed, breadth_eq_sub hl hg he hd⟩

end Elements.Book10
