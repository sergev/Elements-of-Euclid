import SystemE
import Elements.Book6.Prop16

namespace Elements.Book6

open Elements.Book5

/--
If three straight lines are proportional, `ab : cd :: cd : ef`, the rectangle contained by
the outermost is equal to the square on the middle one.
-/
theorem proposition_17 : ∀ (a b c d e f : Point),
  (a─b) ∶ (c─d) ∷ (c─d) ∶ (e─f) → |(a─b)| * |(e─f)| = |(c─d)| * |(c─d)| :=
by
  euclid_intros
  -- with `D` equal to `B` (here `cd` itself), `A : B :: D : C`: the rectangle on `A`, `C`
  -- is equal to that on `B`, `D` [Prop. 6.16], the square on `B`
  exact proposition_16 a b c d c d e f ‹_›

/--
If the rectangle contained by the outermost of three straight lines is equal to the
square on the middle one, the three are proportional: `ab : cd :: cd : ef`.
-/
theorem proposition_17' : ∀ (a b c d e f : Point),
  a ≠ b ∧ c ≠ d ∧ e ≠ f ∧ |(a─b)| * |(e─f)| = |(c─d)| * |(c─d)| →
  (a─b) ∶ (c─d) ∷ (c─d) ∶ (e─f) :=
by
  euclid_intros
  -- the rectangle on `A`, `C` is equal to that on `B`, `D` [Prop. 6.16]
  exact proposition_16' a b c d c d e f ⟨‹_›, ‹_›, ‹_›, ‹_›, ‹_›⟩

end Elements.Book6
