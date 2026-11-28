import Elements.Book8.Prop09

namespace Elements.Book8

open Elements.Book7

/-- As the unit is to `d`, so `x` is to `y`: the unit measures `d` as many times as `x`
measures `y`, so `d` multiplying `x` makes `y` [Def. 7.20]. -/
theorem eq_mul_of_unit {d x y : ℕ} (h : 1 ∶ d ∷ x ∶ y) : y = x * d := by
  obtain ⟨m, n, e, f, -, -, h1, rfl, rfl, rfl⟩ := proportion_iff.mp h
  obtain rfl := Nat.eq_one_of_mul_eq_one_right h1.symm
  obtain rfl := Nat.eq_one_of_mul_eq_one_left h1.symm
  rw [Nat.one_mul, Nat.mul_one]

/-- Numbers `c` continuously proportional from the unit are `powers 1 (c 1)`: each is the
one before multiplied by `c 1` [Def. 7.20]. -/
theorem eq_powers_one {n : ℕ} {c : Fin (n + 1) → ℕ} (hcon : Continued c) (h0 : c 0 = 1) :
    ∀ k (hk : k ≤ n), c ⟨k, by omega⟩ = powers 1 (c 1) k (Fin.last k) := by
  intro k hk
  induction k with
  | zero => exact h0
  | succ k ih =>
    have := hcon ⟨k, by omega⟩
    rw [h0] at this
    rw [powers_last, ← ih (by omega)]
    exact eq_mul_of_unit this.symm

/--
If `n` numbers fall between each of two numbers `a`, `b` and the unit in continued
proportion, then as many fall between `a` and `b` themselves. Euclid has two fall
between; the argument is the same for any multitude. With `d`, `f` next to the unit,
`d` multiplying itself makes the next and so on up to `a`, and `f` up to `b` (Def. 7.20);
then 8.2's numbers in the ratio of `d` to `f` are the ones falling between (`d`
multiplying `f` makes `h`, and `d`, `f` multiplying `h` make `k`, `l`).
-/
theorem proposition_10 {n a b : ℕ} (ha : FallBetween n 1 a) (hb : FallBetween n 1 b) :
    FallBetween n a b := by
  obtain ⟨c, hc, hcon, h0, rfl⟩ := ha
  obtain ⟨c', hc', hcon', h0', rfl⟩ := hb
  -- `d`, multiplying itself and the products, makes `a`; and `f` makes `b`
  have hca := eq_powers_one hcon h0 (n + 1) le_rfl
  have hcb := eq_powers_one hcon' h0' (n + 1) le_rfl
  have hd := hc 1
  have hf := hc' 1
  refine ⟨powers (c 1) (c' 1) (n + 1), powers_pos hd hf _,
    (powers_continuedIn hd hf _).continued (powers_pos hd hf _) hd hf, ?_, ?_⟩
  · rw [powers_zero_eq]
    exact hca.symm
  · rw [powers_last_eq]
    exact hcb.symm

end Elements.Book8
