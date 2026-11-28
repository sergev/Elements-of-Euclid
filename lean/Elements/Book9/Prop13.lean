import Elements.Book9.Prop12

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/-- 9.13 for the numbers up to `a k`: every number measuring `a k` is one of `a 0`, …,
`a k`. -/
theorem measures_eq_of_prime {n : ℕ} {a : Fin (n + 1) → ℕ} (hcon : Continued a)
    (h0 : a 0 = 1) (hp : PrimeNumber (a 1)) {k : ℕ} (hk : k ≤ n) {e : ℕ}
    (he : e ∣ a ⟨k, by omega⟩) : ∃ i, ∃ _ : i ≤ k, e = a ⟨i, by omega⟩ := by
  have h1 := hp.1
  have ha := unit_pos hcon h0 h1
  induction k generalizing e with
  | zero =>
    rw [show (⟨0, by omega⟩ : Fin (n + 1)) = 0 from rfl, h0] at he
    exact ⟨0, le_rfl, (Nat.dvd_one.mp he).trans h0.symm⟩
  | succ k ih =>
    have he0 : 0 < e := Nat.pos_of_ne_zero fun h => by
      obtain ⟨c, hc⟩ := he; have := ha ⟨k + 1, by omega⟩; rw [hc, h, Nat.zero_mul] at this
      omega
    rcases Nat.eq_or_lt_of_le he0 with rfl | he1
    · exact ⟨0, by omega, h0.symm⟩
    -- `e` is prime, or measured by a prime [Prop. 7.32]; that prime measures `a (k + 1)`,
    -- so it measures the prime `a 1` [Prop. 9.12], and it is `a 1`: `a 1` measures `e`
    have h1e : a 1 ∣ e := by
      obtain ⟨q, hq, hqe⟩ : ∃ q, PrimeNumber q ∧ q ∣ e := by
        rcases Elements.Book7.proposition_32 he1 with h | h
        · exact ⟨e, h, measures_self e⟩
        · exact h
      have hq1 := prime_measures_one hcon h0 h1 hq hk (by omega) (measures_trans hqe he)
      rcases hp.2 q hq1 with h | h
      · have := hq.1; omega
      · exact h ▸ hqe
    -- `e` measures `a (k + 1)` according to some `f`, and `a 1` according to `a k`
    -- [Prop. 9.11 corollary]: as `a 1` is to `e`, so `f` is to `a k` [Prop. 7.19]
    obtain ⟨f, hf⟩ := he
    have hf0 : 0 < f := Nat.pos_of_ne_zero fun h => by
      have := ha ⟨k + 1, by omega⟩; rw [hf, h, Nat.mul_zero] at this; omega
    have h11 := proposition_11_corollary hcon h0 h1 (i := 1) (j := k + 1) (by omega) hk
    rw [fin_one_eq (by omega), show (⟨k + 1 - 1, by omega⟩ : Fin (n + 1)) = ⟨k, by omega⟩
      from Fin.ext (by simp only; omega), hf] at h11
    have h19 := proportion_of_mul_eq (ha 1) (ha _) he0 hf0 h11.symm
    -- `a 1` measures `e`, so `f` measures `a k` [Def. 7.20], and `f` is one of them
    obtain ⟨i, hik, hfi⟩ :=
      ih (by omega) (measures_of_proportion (ha 1) he0 hf0 (ha _) h19 h1e)
    -- `a i` measures `a (k + 1)` according to `a (k + 1 - i)` [Prop. 9.11 corollary], and
    -- according to `e`; so `e` is `a (k + 1 - i)` [Prop. 7.16]
    have h11' := proposition_11_corollary hcon h0 h1 (i := i) (j := k + 1) (by omega) hk
    rw [hf, hfi, Elements.Book7.proposition_16 (ha _) he0] at h11'
    exact ⟨k + 1 - i, by omega, Nat.eq_of_mul_eq_mul_left (ha _) h11'⟩

/--
If any multitude of numbers are continuously proportional from a unit, and the number
after the unit is prime, the greatest is measured by none except the proportional
numbers: every number measuring `a n` is some `a i` (the unit is `a 0`, the greatest
`a n` itself).

Euclid argues by contradiction: a number `e` measuring the last, not among them, is
measured by `a 1` (it is not prime, and its prime measures are `a 1` [Props. 7.31, 9.12]),
so is the number `f` according to which it measures, and so on down to the unit
[Props. 9.11, 7.19]. The same steps, taken from the unit up, are an induction: if `f`,
measuring `a k`, is one of them, so is `e` [Prop. 9.11].
-/
theorem proposition_13 {n : ℕ} {a : Fin (n + 1) → ℕ} (hcon : Continued a) (h0 : a 0 = 1)
    (hp : PrimeNumber (a 1)) {e : ℕ} (he : e ∣ a (Fin.last n)) : ∃ i, e = a i := by
  obtain ⟨i, _, h⟩ := measures_eq_of_prime hcon h0 hp le_rfl he
  exact ⟨_, h⟩

end Elements.Book9
