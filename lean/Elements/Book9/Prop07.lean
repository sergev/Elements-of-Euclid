import Elements.Book9.Prop06

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/-- If a composite number `a` multiplying some number `b` makes some number, the number
made is solid. `b` is a number, greater than the unit, as Def. 7.17 needs all three sides
to be. -/
theorem proposition_7 {a b : ℕ} (hb : 1 < b) (ha : CompositeNumber a) :
    SolidNumber (b * a) := by
  -- `a` is measured by some number `d`, according to the units in `e` [Def. 7.13]
  obtain ⟨d, hd, hda, e, rfl⟩ := ha
  have he : 1 < e := Nat.lt_of_not_le fun h => by
    have := Nat.mul_le_mul_left d h
    omega
  -- `e` multiplying `d` makes `a`, and `d * e` multiplying `b` makes `c`: its sides are
  -- `b`, `d`, `e` [Def. 7.17; associativity -- Missed by Euclid.]
  exact ⟨b, d, e, hb, hd, he, (Nat.mul_assoc b d e).symm⟩

end Elements.Book9
