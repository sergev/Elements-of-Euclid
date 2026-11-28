import Elements.Book9.Prop25

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/-- If an odd number `b` is subtracted from an odd number `a`, the remainder is even. -/
theorem proposition_26 {a b : ℕ} (ha : OddNumber a) (hb : OddNumber b) (hba : b < a) :
    EvenNumber (a - b) := by
  -- let the unit be taken from `a`: the remainder is even [Def. 7.7]
  have ha' := ha.sub_unit (by have := hb.1; omega)
  rcases Nat.eq_or_lt_of_le hb.1 with rfl | hb1
  · exact ha'
  · -- and taken from `b`, the remainder is even; so the remainder of the remainders,
    -- `a - b`, is even [Prop. 9.24]
    have h := proposition_24 ha' (hb.sub_unit hb1) (by omega)
    rwa [show a - 1 - (b - 1) = a - b by omega] at h

end Elements.Book9
