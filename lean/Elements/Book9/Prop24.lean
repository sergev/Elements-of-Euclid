import Elements.Book9.Prop23

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/-- If an even number `b` is subtracted from an even number `a`, the remainder is even:
each has a half, and so the remainder has a half. -/
theorem proposition_24 {a b : ℕ} (ha : EvenNumber a) (hb : EvenNumber b) (hba : b < a) :
    EvenNumber (a - b) := by
  -- each has a half part [Def. 7.6]
  obtain ⟨h, -, rfl⟩ := ha
  obtain ⟨k, -, rfl⟩ := hb
  -- and hence the remainder has a half part, the remainder of the halves
  exact ⟨h - k, by omega, by omega⟩

end Elements.Book9
