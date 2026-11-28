import Elements.Book7.Prop30

namespace Elements.Book7

/-- A number greater than the unit that is not prime is composite (Defs. 7.11, 7.13). -/
theorem composite_of_not_prime {a : ℕ} (ha : 1 < a) (h : ¬ PrimeNumber a) :
    CompositeNumber a := by
  simp only [PrimeNumber, ha, true_and, not_forall, not_or] at h
  obtain ⟨d, hd, hd1, hda⟩ := h
  have := le_of_measures (by omega) hd
  have := Nat.pos_of_dvd_of_pos hd (by omega)
  exact ⟨d, by omega, by omega, hd⟩

/-- Every composite number `a` is measured by some prime number. -/
theorem proposition_31 {a : ℕ} (h : CompositeNumber a) : ∃ p, PrimeNumber p ∧ p ∣ a := by
  -- Euclid's descent: if no prime is found, an infinite series of numbers, each less than
  -- the one before, measures `a`, which is impossible in numbers. So, by induction on the
  -- number: a prime measures every composite number less than `a`
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  -- some number `b` measures `a`
  obtain ⟨b, hb1, hba, hb⟩ := h
  -- if `b` is prime, it is found
  by_cases hbp : PrimeNumber b
  · exact ⟨b, hbp, hb⟩
  -- if `b` is composite, some prime `p` measures it, and so `a`
  obtain ⟨p, hp, hpb⟩ := ih b hba (composite_of_not_prime hb1 hbp)
  exact ⟨p, hp, measures_trans hpb hb⟩

end Elements.Book7
