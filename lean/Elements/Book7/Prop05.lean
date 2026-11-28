import Elements.Book7.Prop04

namespace Elements.Book7

/-- Euclid's argument: `a` taken `n` times and `d` taken as many times are together `a`
and `d` taken `n` times, each of the `n` divisions being `a` and `d`. -/
theorem proposition_5' (a d n : ℕ) : a * n + d * n = (a + d) * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.mul_succ, Nat.mul_succ, Nat.mul_succ, ← ih]
    omega

/-- If `a` is part of `b`, and `d` is the same part of `e`, then `a + d` is the same part
of `b + e`. -/
theorem proposition_5 {a b d e n : ℕ} (h₁ : PartOf a b n) (h₂ : PartOf d e n) :
    PartOf (a + d) (b + e) n :=
  ⟨h₁.1, by rw [h₁.2, h₂.2, proposition_5']⟩

end Elements.Book7
