import Elements.Book9.Prop21

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/--
If any multitude of odd numbers are added together, and their multitude is even, the
whole is even.

A unit taken from each leaves an even number [Def. 7.7], or nothing when the odd number
is the unit; so the remainders added together are halved as in 9.21, and so are the
units, an even multitude.
-/
theorem proposition_22 {n : ℕ} {a : Fin (n + 1) → ℕ} (ha : ∀ i, OddNumber (a i))
    (hn : EvenNumber (n + 1)) : EvenNumber (sum a) := by
  -- a unit taken from each leaves two halves [Def. 7.7]
  choose h hah using fun i => odd_iff.mp (ha i)
  -- the remainders added together have a half [Prop. 9.21], and the units, an even
  -- multitude, have a half
  obtain ⟨m, hm, hnm⟩ := hn
  have hs : sum a = sum h + sum h + sum (fun _ : Fin (n + 1) => 1) := by
    rw [← sum_add, ← sum_add]
    exact congrArg sum (funext hah)
  rw [sum_const, Nat.one_mul] at hs
  -- so the whole has a half [Prop. 9.21]
  exact ⟨sum h + m, by omega, by omega⟩

end Elements.Book9
