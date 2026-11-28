import Elements.Book5.Prop09
import Elements.Book5.Prop10
import Elements.Book5.Prop11
import Elements.Book5.Prop13

namespace Elements.Book5

variable {M : Type*} [Magnitude M]

/--
If `A : B :: C : D`, and the first `A` is greater than the third `C`, then the second `B`
is greater than the fourth `D`; if equal, equal; if less, less.
-/
theorem proposition_14 {a b c d : M} (h : Proportion a b c d) :
    (c < a → d < b) ∧ (a = c → b = d) ∧ (a < c → b < d) := by
  have gt : ∀ {a b c d : M}, Proportion a b c d → c < a → d < b := by
    intro a b c d h hca
    -- `A` has a greater ratio to `B` than `C` has to `B` [Prop. 5.8]
    have h₁ := (proposition_8 hca b).1
    -- so `C` has a greater ratio to `D` than `C` to `B` [Prop. 5.13]
    have h₂ := proposition_13 h.symm h₁
    -- and that to which the same has the greater ratio is the lesser [Prop. 5.10]
    exact proposition_10' h₂
  refine ⟨gt h, fun hac => ?_, gt h.symm⟩
  -- similarly, if `A` is equal to `C`: `A : B :: C : B` [Prop. 5.7], so `C : D :: C : B`
  -- [Prop. 5.11], and `D` is equal to `B` [Prop. 5.9]
  have h₁ := (proposition_7 b hac).1
  exact (proposition_9' (proposition_11 h.symm h₁)).symm
