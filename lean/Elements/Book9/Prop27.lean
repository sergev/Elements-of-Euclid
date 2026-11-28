import Elements.Book9.Prop26

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/-- If an even number `b` is subtracted from an odd number `a`, the remainder is odd. -/
theorem proposition_27 {a b : ℕ} (ha : OddNumber a) (hb : EvenNumber b) (hba : b < a) :
    OddNumber (a - b) := by
  -- let the unit be taken from `a`: the remainder is even [Def. 7.7]
  have hb1 := hb.one_lt
  have ha' := ha.sub_unit (by omega)
  rcases Nat.eq_or_lt_of_le (show b ≤ a - 1 by omega) with h | h
  · -- `b` is all of it: what is left is the unit
    rw [show a - b = 1 by omega]
    exact odd_iff.mpr ⟨0, rfl⟩
  · -- `b` taken from it leaves an even number [Prop. 9.24], and with the unit, `a - b` is
    -- odd [Def. 7.7]
    have := (proposition_24 ha' hb h).add_unit
    rwa [show a - 1 - b + 1 = a - b by omega] at this

end Elements.Book9
