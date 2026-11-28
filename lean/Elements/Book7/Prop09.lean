import Elements.Book7.Prop08

namespace Elements.Book7

/-- Euclid's argument: `n` numbers, each `x` taken `p` times, are together `x` taken `n`
times, taken `p` times [Props. 7.5, 7.6]. -/
theorem mul_swap (x p n : ℕ) : x * p * n = x * n * p := by
  induction n with
  | zero => rw [Nat.mul_zero, Nat.mul_zero, Nat.zero_mul]
  | succ n ih => rw [Nat.mul_succ, Nat.mul_succ, ih, proposition_5']

/--
If `a` is part of `b`, and `d` is the same part of `e`, then, alternately, whichever part,
or parts, `a` is of `d`, `b` is the same part, or parts, of `e`: `a ∶ d ∷ b ∶ e`
(Def. 7.20). Stated for the unit as well.
-/
theorem proposition_9 {a b d e n : ℕ} (ha : 0 < a) (hd : 0 < d) (h₁ : PartOf a b n)
    (h₂ : PartOf d e n) : a ∶ d ∷ b ∶ e := by
  obtain ⟨-, rfl⟩ := h₁
  obtain ⟨-, rfl⟩ := h₂
  -- `a` is parts of `d`, of its units if of nothing else [Prop. 7.4]
  refine proportion_iff.mpr ⟨a, d, 1, n, ha, hd, (Nat.one_mul a).symm,
    (Nat.one_mul d).symm, ?_, ?_⟩
  -- `b` divided into `n` numbers equal to `a`, and `e` into `n` equal to `d`: each is
  -- the same parts of the other, and so are the sums [Props. 7.5, 7.6]
  · simpa only [Nat.one_mul] using mul_swap 1 a n
  · simpa only [Nat.one_mul] using mul_swap 1 d n

end Elements.Book7
