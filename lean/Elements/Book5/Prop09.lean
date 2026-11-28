import Elements.Book5.Prop08

namespace Elements.Book5

open Magnitude

variable {M : Type*} [Magnitude M]

/-- Magnitudes `A`, `B` having the same ratio to the same `C` are equal. -/
theorem proposition_9 {a b c : M} (h : Proportion a c b c) : a = b := by
  -- if not, they would not have the same ratio to `C` [Prop. 5.8]
  by_contra hne
  rcases lt_or_gt_of_ne hne with h' | h'
  · exact h.symm.not_greaterRatio (proposition_8 h' c).1
  · exact h.not_greaterRatio (proposition_8 h' c).1

/-- Magnitudes `A`, `B` to which the same `C` has the same ratio are equal. -/
theorem proposition_9' {a b c : M} (h : Proportion c a c b) : a = b := by
  -- if not, `C` would not have the same ratio to them [Prop. 5.8]
  by_contra hne
  rcases lt_or_gt_of_ne hne with h' | h'
  · exact h.not_greaterRatio (proposition_8 h' c).2
  · exact h.symm.not_greaterRatio (proposition_8 h' c).2
