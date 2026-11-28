import Elements.Book10.Prop086

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- To find a third apotome, relative to a rational line `r` laid out: the same
construction as 10.50, the lesser term taken from the greater [Def. 10.III.3]. -/
theorem proposition_87 {r : Length} (hr : Rational ρ r) : ∃ l, ThirdApotome ρ r l := by
  obtain ⟨-, x, y, h, -⟩ := proposition_50 hr
  obtain ⟨l, hl⟩ := Magnitude.remainder y x h.1.2.2.2
  exact ⟨l, x, y, h, (add_comm l y).trans hl⟩

end Elements.Book10
