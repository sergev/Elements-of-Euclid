import Elements.Book10.Prop092

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- If an area is contained by a rational line `r` and a third apotome, the square root
`z` of the area is a second apotome of a medial. The same construction as 10.56, the terms
of 10.56 taken one from the other. -/
theorem proposition_93 {r l z : Length} (hr : Rational ρ r) (hl : ThirdApotome ρ r l)
    (hz : sq z = rect r l) : SecondApotomeOfMedial ρ z := by
  -- the whole `x` and the attached `y` [Def. 10.III.3]: as in 10.56, terms `m > n`
  obtain ⟨x, y, h, hl⟩ := hl
  obtain ⟨m, n, h, hsum, htwice⟩ := proposition_56_terms hr h
  -- `m - n` is the square root of the area [Props. 10.53 lem., 2.7]
  exact ⟨m, n, h, side_eq_sub hsum htwice hl hz h.2.2.2.2⟩

end Elements.Book10
