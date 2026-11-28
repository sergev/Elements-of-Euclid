import Elements.Book7.Prop31

namespace Elements.Book7

/-- Every number `a` is either prime or measured by some prime number. -/
theorem proposition_32 {a : ℕ} (ha : 1 < a) :
    PrimeNumber a ∨ ∃ p, PrimeNumber p ∧ p ∣ a := by
  -- if `a` is prime, it is so; if composite, some prime measures it [Prop. 7.31]
  by_cases h : PrimeNumber a
  · exact Or.inl h
  · exact Or.inr (proposition_31 (composite_of_not_prime ha h))

end Elements.Book7
