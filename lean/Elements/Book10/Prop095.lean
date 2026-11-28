import Elements.Book10.Prop094

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- If an area is contained by a rational line `r` and a fifth apotome, the square root
`z` of the area is that which with a rational area makes a medial whole. The same
construction as 10.58, the terms of 10.58 taken one from the other. -/
theorem proposition_95 {r l z : Length} (hr : Rational ρ r) (hl : FifthApotome ρ r l)
    (hz : sq z = rect r l) : MedialWholeWithRational ρ z := by
  -- the whole `x` and the attached `y` [Def. 10.III.5]: as in 10.58, terms `m > n`
  obtain ⟨x, y, h, hl⟩ := hl
  obtain ⟨m, n, h, hsum, htwice⟩ := proposition_58_terms hr h
  -- `m - n` is the square root of the area [Props. 10.53 lem., 2.7]
  exact ⟨m, n, h, side_eq_sub hsum htwice hl hz h.2.2.2⟩

end Elements.Book10
