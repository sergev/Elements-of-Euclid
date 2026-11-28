import Elements.Book10.Prop097

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- The square on a first apotome of a medial, applied to a rational line `r`, makes as
breadth a second apotome. The same construction as 10.61, the breadth of twice the
rectangle taken from that of the squares. -/
theorem proposition_98 {r l g : Length} (hl : FirstApotomeOfMedial ρ l)
    (hr : Rational ρ r) (hg : rect r g = sq l) : SecondApotome ρ r g := by
  obtain ⟨x, y, h, hl⟩ := hl
  obtain ⟨e, d, hed, he, hd⟩ := proposition_61_terms hr h
  -- the breadth is `e - d` [Prop. 2.7]
  exact ⟨e, d, hed, breadth_eq_sub hl hg he hd⟩

end Elements.Book10
