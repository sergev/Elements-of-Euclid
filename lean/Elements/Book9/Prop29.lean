import Elements.Book9.Prop28

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/-- If an odd number `a` multiplying an odd number `b` makes some number, the number made
is odd. -/
theorem proposition_29 {a b : ℕ} (ha : OddNumber a) (hb : OddNumber b) :
    OddNumber (b * a) := by
  -- it is made of as many numbers equal to `b` as there are units in `a` [Def. 7.15]: odd
  -- numbers, an odd multitude, so it is odd [Prop. 9.23]
  rw [mul_eq_sum b ha.1]
  exact proposition_23 (fun _ => hb) (by rwa [show a - 1 + 1 = a by have := ha.1; omega])

end Elements.Book9
