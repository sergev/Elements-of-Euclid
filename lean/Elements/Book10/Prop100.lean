import Elements.Book10.Prop099

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- The square on a minor line, applied to a rational line `r`, makes as breadth a
fourth apotome. The same construction as 10.63, the breadth of twice the rectangle
taken from that of the squares. -/
theorem proposition_100 {r l g : Length} (hl : Minor ρ l) (hr : Rational ρ r)
    (hg : rect r g = sq l) : FourthApotome ρ r g := by
  obtain ⟨x, y, h, hl⟩ := hl
  obtain ⟨e, d, hed, he, hd⟩ := proposition_63_terms hr h
  -- the breadth is `e - d` [Prop. 2.7]
  exact ⟨e, d, hed, breadth_eq_sub hl hg he hd⟩

end Elements.Book10
