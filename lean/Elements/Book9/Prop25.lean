import Elements.Book9.Prop24

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/-- If an odd number `b` is subtracted from an even number `a`, the remainder is odd. -/
theorem proposition_25 {a b : ℕ} (ha : EvenNumber a) (hb : OddNumber b) (hba : b < a) :
    OddNumber (a - b) := by
  rcases Nat.eq_or_lt_of_le hb.1 with rfl | hb1
  · -- the unit taken from an even number leaves an odd number [Def. 7.7]
    exact ha.sub_unit
  · -- let the unit be taken from `b`: the remainder is even [Def. 7.7], and taken from
    -- `a` it leaves an even number [Prop. 9.24]; and the unit taken from that leaves
    -- `a - b`, odd [Def. 7.7]
    have h := proposition_24 ha (hb.sub_unit hb1) (by omega)
    have := h.sub_unit
    rwa [show a - (b - 1) - 1 = a - b by omega] at this

end Elements.Book9
