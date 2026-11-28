import Elements.Book10.Prop007

namespace Elements.Book10

open Elements.Book5

variable {M : Type*} [Magnitude M]

/-- If two magnitudes do not have to one another the ratio which a number has to a number,
they are incommensurable. -/
theorem proposition_8 {a b : M}
    (h : ¬ ∃ m n : ℕ+, Proportion a b (m : Number) (n : Number)) : ¬ Commensurable a b :=
  -- else `a` has to `b` the ratio which a number has to a number [Prop. 10.5]
  fun h' => h (proposition_5 h')

end Elements.Book10
