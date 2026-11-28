import Elements.Book9.Prop20

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/-- If any multitude of even numbers are added together, the whole is even: each has a
half, and so the whole has a half, the halves added together. -/
theorem proposition_21 {n : ℕ} {a : Fin (n + 1) → ℕ} (ha : ∀ i, EvenNumber (a i)) :
    EvenNumber (sum a) := by
  -- each has a half part [Def. 7.6]
  choose h hh hah using ha
  -- and hence the whole has a half part
  refine ⟨sum h, sum_pos hh, ?_⟩
  rw [← sum_add]
  exact congrArg sum (funext hah)

end Elements.Book9
