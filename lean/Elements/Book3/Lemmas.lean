import SystemE

/-
Facts about squares that Book 3 takes for granted with Prop. 1.47: equal squares
are on equal lines (as in Prop. 1.48), and the greater square on the greater line.
-/

namespace Elements.Book3

theorem length_eq_of_square_eq : ∀ (a b c d : Point),
  |(a─b)| * |(a─b)| = |(c─d)| * |(c─d)| → |(a─b)| = |(c─d)| :=
by
  intro a b c d h
  exact (mul_self_inj (segment_gte_zero _) (segment_gte_zero _)).1 h

theorem square_lt_of_lt : ∀ (a b c d : Point),
  |(a─b)| < |(c─d)| → |(a─b)| * |(a─b)| < |(c─d)| * |(c─d)| :=
by
  intro a b c d h
  exact mul_self_lt_mul_self (segment_gte_zero _) h

theorem lt_of_square_lt : ∀ (a b c d : Point),
  |(a─b)| * |(a─b)| < |(c─d)| * |(c─d)| → |(a─b)| < |(c─d)| :=
by
  intro a b c d h
  exact lt_of_mul_self_lt_mul_self₀ (segment_gte_zero _) h

end Elements.Book3
