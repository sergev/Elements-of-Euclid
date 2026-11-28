import Elements.Book10.Prop100

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- The square on that which with a rational area makes a medial whole, applied to a
rational line `r`, makes as breadth a fifth apotome. The same construction as 10.64, the
breadth of twice the rectangle taken from that of the squares. -/
theorem proposition_101 {r l g : Length} (hl : MedialWholeWithRational ρ l)
    (hr : Rational ρ r) (hg : rect r g = sq l) : FifthApotome ρ r g := by
  obtain ⟨x, y, h, hl⟩ := hl
  obtain ⟨e, d, hed, he, hd⟩ := proposition_64_terms hr h
  -- the breadth is `e - d` [Prop. 2.7]
  exact ⟨e, d, hed, breadth_eq_sub hl hg he hd⟩

end Elements.Book10
