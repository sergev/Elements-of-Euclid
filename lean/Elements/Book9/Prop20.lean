import Elements.Book9.Prop19

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/--
The prime numbers are more than any assigned multitude of them: for any primes `p 0`, …,
`p n`, some prime is none of them. Euclid takes three primes; the argument is the same for
any multitude.
-/
theorem proposition_20 {n : ℕ} {p : Fin (n + 1) → ℕ} (hp : ∀ i, PrimeNumber (p i)) :
    ∃ q, PrimeNumber q ∧ ∀ i, q ≠ p i := by
  have hp0 : ∀ i, 0 < p i := fun i => by have := (hp i).1; omega
  -- the least number `d` measured by them [Prop. 7.36], and the unit added to it
  obtain ⟨d, hd⟩ := exists_leastMeasuredSeq hp0
  have hd0 := hd.1
  -- a prime measuring `d + 1` is none of them: else it would measure `d`, and the
  -- remainder, the unit [Prop. 7.28]
  have hnot : ∀ g, PrimeNumber g → g ∣ d + 1 → ∀ i, g ≠ p i := by
    rintro g hg hgd i rfl
    have h1 := measures_sub hgd (hd.2.1 i)
    rw [Nat.add_sub_cancel_left] at h1
    have := le_of_measures Nat.one_pos h1
    have := hg.1
    omega
  -- `d + 1` is prime, or not
  by_cases hE : PrimeNumber (d + 1)
  · exact ⟨d + 1, hE, hnot _ hE (measures_self _)⟩
  · -- if not, it is measured by some prime `g` [Prop. 7.31]
    obtain ⟨g, hg, hgd⟩ := Elements.Book7.proposition_31
      (Elements.Book7.composite_of_not_prime (by omega) hE)
    exact ⟨g, hg, hnot g hg hgd⟩

end Elements.Book9
