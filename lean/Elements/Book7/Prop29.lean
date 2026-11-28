import Elements.Book7.Prop28

namespace Elements.Book7

/-- A prime number `a` is prime to every number `b` it does not measure. -/
theorem proposition_29 {a b : ℕ} (ha : PrimeNumber a) (h : ¬ a ∣ b) : PrimeTo b a := by
  -- if not, some number `c` measures `b` and `a`
  intro c hcb hca
  -- `c` measures `b`, and `a` does not: `c` is not `a`; but it measures `a`, which is
  -- prime
  rcases ha.2 c hca with hc | rfl
  · exact hc
  · exact absurd hcb h

end Elements.Book7
