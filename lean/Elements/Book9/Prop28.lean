import Elements.Book9.Prop27

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/-- `b` multiplied by `a` is as many numbers equal to `b` as there are units in `a`,
added together (Def. 7.15). -/
theorem mul_eq_sum (b : ℕ) {a : ℕ} (ha : 0 < a) :
    b * a = sum (fun _ : Fin (a - 1 + 1) => b) := by
  rw [sum_const, show a - 1 + 1 = a by omega]

/-- If an odd number `a` multiplying an even number `b` makes some number, the number
made is even. -/
theorem proposition_28 {a b : ℕ} (ha : OddNumber a) (hb : EvenNumber b) :
    EvenNumber (b * a) := by
  -- it is made of as many numbers equal to `b` as there are units in `a` [Def. 7.15], and
  -- `b` is even: so it is even [Prop. 9.21]
  rw [mul_eq_sum b ha.1]
  exact proposition_21 fun _ => hb

end Elements.Book9
