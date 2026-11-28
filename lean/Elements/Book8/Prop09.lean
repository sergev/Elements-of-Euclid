import Elements.Book8.Prop08

namespace Elements.Book8

open Elements.Book7

/-- From the unit: `powers 1 a k` are the unit, `a`, `a * a`, …, continuously
proportional in the ratio of the unit to `a`. The first is the unit. -/
theorem powers_one_zero (a k : ℕ) : powers 1 a k 0 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [powers_zero, ih]

/-- The first of `powers a b k` is the last from the unit in the ratio of the unit to `a`
(`a` made by multiplying itself `k` times, 8.2's corollary). -/
theorem powers_zero_eq (a b k : ℕ) : powers a b k 0 = powers 1 a k (Fin.last k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [powers_zero, powers_last, ih]

/-- The last of `powers a b k` is the last from the unit in the ratio of the unit to
`b`. -/
theorem powers_last_eq (a b k : ℕ) :
    powers a b k (Fin.last k) = powers 1 b k (Fin.last k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [powers_last, powers_last, ih]

/-- The numbers from the unit, `powers 1 a k`, fall between the unit and the last. -/
theorem fallBetween_unit {a : ℕ} (ha : 0 < a) (n : ℕ) :
    FallBetween n 1 (powers 1 a (n + 1) (Fin.last _)) :=
  ⟨_, powers_pos Nat.one_pos ha _,
    (powers_continuedIn Nat.one_pos ha _).continued (powers_pos Nat.one_pos ha _)
      Nat.one_pos ha,
    powers_one_zero a _, rfl⟩

/--
If two numbers `a`, `b` are prime to one another and `n` numbers fall between them in
continued proportion, then as many fall between each of them and the unit. Euclid has two
fall between; the argument is the same for any multitude.
-/
theorem proposition_9 {n a b : ℕ} (hab : PrimeTo a b) (h : FallBetween n a b) :
    FallBetween n 1 a ∧ FallBetween n 1 b := by
  obtain ⟨c, hc, hcon, rfl, rfl⟩ := h
  -- `a`, …, `b` are the least having the same ratio [Prop. 8.1]; so they are the least
  -- numbers in the ratio of some `f` to `g` [Props. 7.33, 8.2]
  obtain ⟨f, g, hf, hg, -, rfl⟩ := eq_powers hc hcon (proposition_1 hc hab)
  -- `f` multiplying itself and the products makes `a`, and `g` makes `b` [Prop. 8.2
  -- corollary]: as the unit is to `f`, so `f` is to `f * f`, and so on [Def. 7.20]
  rw [powers_zero_eq, powers_last_eq f g]
  exact ⟨fallBetween_unit hf n, fallBetween_unit hg n⟩

end Elements.Book8
