import Elements.Book9.Prop11

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/-- Euclid's step in 9.12 and 9.13: if `a` multiplying `c` makes what `e` multiplying `f`
makes, then as `a` is to `e`, so `f` is to `c` [Props. 7.16, 7.19]. -/
theorem proportion_of_mul_eq {a c e f : ℕ} (ha : 0 < a) (hc : 0 < c) (he : 0 < e)
    (hf : 0 < f) (h : a * c = e * f) : a ∶ e ∷ f ∶ c := by
  rw [Elements.Book7.proposition_19 ha he hf hc, Elements.Book7.proposition_16 ha hc, h,
    Elements.Book7.proposition_16 he hf]

/-- If a prime `p` prime to `a 1` measures `a (k + 1)`, it measures `a k`: `a 1`
multiplying `a k` makes `a (k + 1)` [Prop. 9.11 corollary], and so does `p` multiplying
some `f`; so as `a 1` is to `p`, so `f` to `a k` [Prop. 7.19], and `a 1`, `p`, prime to
one another, are the least [Prop. 7.21], and measure `f`, `a k` equally [Prop. 7.20]. -/
theorem prime_measures_prev {n : ℕ} {a : Fin (n + 1) → ℕ} (hcon : Continued a)
    (h0 : a 0 = 1) (h1 : 1 < a 1) {p : ℕ} (hp : PrimeNumber p) (hpr : PrimeTo (a 1) p)
    {k : ℕ} (hk : k + 1 ≤ n) (hk0 : 0 < k) (h : p ∣ a ⟨k + 1, by omega⟩) :
    p ∣ a ⟨k, by omega⟩ := by
  have ha := unit_pos hcon h0 h1
  have hp0 : 0 < p := by have := hp.1; omega
  -- `p` measures `a (k + 1)` according to some `f`
  obtain ⟨f, hf⟩ := h
  have hf0 : 0 < f := Nat.pos_of_ne_zero fun h => by
    have := ha ⟨k + 1, by omega⟩; rw [hf, h, Nat.mul_zero] at this; omega
  -- `a 1` measures `a (k + 1)` according to `a k` [Prop. 9.11 corollary]
  have h11 := proposition_11_corollary hcon h0 h1 (i := 1) (j := k + 1) (by omega) hk
  rw [fin_one_eq (by omega), show (⟨k + 1 - 1, by omega⟩ : Fin (n + 1)) = ⟨k, by omega⟩
    from Fin.ext (by simp only; omega), hf] at h11
  -- as `a 1` is to `p`, so `f` is to `a k` [Prop. 7.19]
  have h19 := proportion_of_mul_eq (ha 1) (ha _) hp0 hf0 h11.symm
  -- `a 1`, `p` are the least in their ratio [Prop. 7.21], so `p` measures `a k`
  -- [Prop. 7.20]
  obtain ⟨m, -, hm⟩ := Elements.Book7.proposition_20 hf0 (ha _) (ha 1) hp0
    (Elements.Book7.proposition_21 (ha 1) hp0 hpr) h19
  exact ⟨m, hm⟩

/-- A prime measuring any of the numbers from a unit measures the number after the unit:
9.12 for the numbers up to `a k`. -/
theorem prime_measures_one {n : ℕ} {a : Fin (n + 1) → ℕ} (hcon : Continued a)
    (h0 : a 0 = 1) (h1 : 1 < a 1) {p : ℕ} (hp : PrimeNumber p) {k : ℕ} (hk : k ≤ n)
    (hk0 : 0 < k) (h : p ∣ a ⟨k, by omega⟩) : p ∣ a 1 := by
  -- if not, `p` is prime to `a 1` [Prop. 7.29]
  by_contra hnot
  have hpr := Elements.Book7.proposition_29 hp hnot
  -- `p` measures `a k`, and so the one before it, and so on, down to `a 1`
  apply hnot
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk'
    · rwa [fin_one_eq hk] at h
    · exact ih (by omega) hk' (prime_measures_prev hcon h0 h1 hp hpr hk hk' h)

/--
If any multitude of numbers are continuously proportional from a unit, every prime that
measures the last also measures the number after the unit. The number after the unit is a
number, greater than the unit, and the last is not the unit.

Euclid has `a 1`, …, `a 4` and goes down from the last one step at a time, `e` measuring
`c`, then `b`, then `a`: the proof is by induction.
-/
theorem proposition_12 {n : ℕ} {a : Fin (n + 1) → ℕ} (hcon : Continued a) (h0 : a 0 = 1)
    (h1 : 1 < a 1) (hn : 0 < n) {p : ℕ} (hp : PrimeNumber p)
    (h : p ∣ a (Fin.last n)) : p ∣ a 1 :=
  prime_measures_one hcon h0 h1 hp le_rfl hn h

end Elements.Book9
