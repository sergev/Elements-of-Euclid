import Elements.Book10.Prop090

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- The square on `m - n` is the rectangle contained by `r` and `x - y`: the squares on
`m`, `n` exceed twice the rectangle by it [Prop. 2.7]. -/
theorem side_eq_sub {r x y l m n z : Length} (h₁ : sq m + sq n = rect r x)
    (h₂ : (2 : ℕ+) • rect m n = rect r y) (hl : l + y = x) (hz : sq z = rect r l)
    (hnm : n < m) : z + n = m := by
  obtain ⟨k, hk⟩ := Magnitude.remainder n m hnm
  have h₃ := sq_add_sq_of_sub ((add_comm k n).trans hk)
  rw [h₁, h₂, ← hl, rect_add, add_comm] at h₃
  have hkz : k = z := sq_inj ((add_left_cancel h₃).symm.trans hz.symm)
  rw [← hkz, add_comm]
  exact hk

/-- If an area is contained by a rational line `r` and a first apotome, the square root
`z` of the area is an apotome. The same construction as 10.54, the terms of 10.54 taken
one from the other. -/
theorem proposition_91 {r l z : Length} (hr : Rational ρ r) (hl : FirstApotome ρ r l)
    (hz : sq z = rect r l) : Apotome ρ z := by
  -- the whole `x` and the attached `y` [Def. 10.III.1]: as in 10.54, terms `m > n`
  obtain ⟨x, y, h, hl⟩ := hl
  obtain ⟨m, n, h, hsum, htwice⟩ := proposition_54_terms hr h
  -- `m - n` is the square root of the area [Props. 10.53 lem., 2.7]
  exact ⟨m, n, h, side_eq_sub hsum htwice hl hz h.2.2.2⟩

end Elements.Book10
