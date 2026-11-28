import Elements.Book9.Prop13

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/-- If a least number `a` is measured by prime numbers `p 0`, …, `p n`, it is measured by
no other prime. Euclid takes three primes; the argument is the same for any multitude. -/
theorem proposition_14 {n : ℕ} {p : Fin (n + 1) → ℕ} {a q : ℕ}
    (hp : ∀ i, PrimeNumber (p i)) (ha : LeastMeasuredSeq a p) (hq : PrimeNumber q)
    (hqa : q ∣ a) : ∃ i, q = p i := by
  -- if possible, let `q` be none of them
  by_contra hne'
  have hne : ∀ i, q ≠ p i := fun i h => hne' ⟨i, h⟩
  have hq0 : 0 < q := by have := hq.1; omega
  -- `q` measures `a` according to some `f`
  obtain ⟨f, hf⟩ := hqa
  have hf0 : 0 < f := Nat.pos_of_ne_zero fun h => by
    have := ha.1; rw [hf, h, Nat.mul_zero] at this; omega
  -- each `p i` measures `q * f`, so it measures `q` or `f` [Prop. 7.30]; not `q`, which
  -- is prime and none of them: so each measures `f`
  have hpf : ∀ i, p i ∣ f := fun i => by
    have h := ha.2.1 i
    rw [hf] at h
    rcases Elements.Book7.proposition_30 hf0 hq0 (hp i) h with h' | h'
    · exact h'
    · rcases hq.2 _ h' with h1 | h1
      · have := (hp i).1; omega
      · exact absurd h1.symm (hne i)
  -- and `f` is less than `a`: impossible, `a` being the least they measure
  have := ha.2.2 f hf0 hpf
  have := lt_mul hf0 hq.1
  rw [Elements.Book7.proposition_16 hq0 hf0, ← hf] at this
  omega

end Elements.Book9
