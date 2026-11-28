import Elements.Book10.Prop096

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- In the construction of 10.60, the square on `x - y` applied to `r` makes as breadth
the breadth of the squares less that of twice the rectangle [Prop. 2.7]. -/
theorem breadth_eq_sub {r x y l g e d : Length} (hl : l + y = x) (hg : rect r g = sq l)
    (h₁ : rect r e = sq x + sq y) (h₂ : rect r d = (2 : ℕ+) • rect x y) : g + d = e :=
  rect_inj (by rw [rect_add, hg, h₂, h₁, sq_add_sq_of_sub hl, add_comm])

/-- The square on an apotome, applied to a rational line `r`, makes as breadth a
first apotome. The same construction as 10.60, the breadth of twice the rectangle
taken from that of the squares. -/
theorem proposition_97 {r l g : Length} (hl : Apotome ρ l) (hr : Rational ρ r)
    (hg : rect r g = sq l) : FirstApotome ρ r g := by
  obtain ⟨x, y, h, hl⟩ := hl
  obtain ⟨e, d, hed, he, hd⟩ := proposition_60_terms hr h
  -- the breadth is `e - d` [Prop. 2.7]
  exact ⟨e, d, hed, breadth_eq_sub hl hg he hd⟩

end Elements.Book10
