import Elements.Book10.Prop006

namespace Elements.Book10

open Elements.Book5

variable {M : Type*} [Magnitude M]

/-- Incommensurable magnitudes do not have to one another the ratio which a number has to
a number. As in 10.6, `a` can be divided into any number of equal parts. -/
theorem proposition_7 {a b : M} (h : ¬ Commensurable a b)
    (hpart : ∀ m : ℕ+, ∃ c, a = m • c) :
    ¬ ∃ m n : ℕ+, Proportion a b (m : Number) (n : Number) := by
  -- else `a` is commensurable with `b` [Prop. 10.6]
  rintro ⟨m, n, h'⟩
  exact h (proposition_6 h' (hpart m))

end Elements.Book10
