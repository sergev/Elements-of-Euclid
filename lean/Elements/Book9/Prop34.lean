import Elements.Book9.Prop33

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/-- Cut in half continually: every number, or the unit, is doubled from the unit, or is
such a number multiplied by an odd number. By induction on the number, as in 7.31: a
number not odd has a half, less than itself. -/
theorem halve_continually {a : ℕ} (ha : 0 < a) :
    (∃ k, a = powers 1 2 k (Fin.last k)) ∨
      ∃ k m, a = powers 1 2 k (Fin.last k) * m ∧ OddNumber m ∧ 1 < m := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    rcases even_or_odd ha with ⟨h, hh, rfl⟩ | hodd
    · -- cut in half
      rcases ih h (by omega) hh with ⟨k, hk⟩ | ⟨k, m, hk, hm, hm1⟩
      · exact Or.inl ⟨k + 1, by rw [powers_last, ← hk]; omega⟩
      · -- [Prop. 7.16; associativity -- Missed by Euclid.]
        refine Or.inr ⟨k + 1, m, ?_, hm, hm1⟩
        rw [powers_last, Nat.mul_right_comm, ← hk]
        omega
    · rcases Nat.eq_or_lt_of_le ha with rfl | ha1
      · exact Or.inl ⟨0, rfl⟩
      · exact Or.inr ⟨0, a, (Nat.one_mul a).symm, hodd, ha1⟩

/--
If an even number `a` is neither doubled from a dyad nor has an odd half, it is both
even-times-even and even-times-odd.

Euclid assumes the number even; it is a hypothesis. His first step, "even-times-even, for
it does not have an odd half" [Def. 7.8], holds as Def. 7.8 is stated: the half is even,
and the dyad measures `a` according to it. "Cut in half continually" is a descent, an
induction on the number.
-/
theorem proposition_34 {a : ℕ} (ha : EvenNumber a)
    (hd : ∀ k, a ≠ powers 1 2 k (Fin.last k)) (hh : ¬ ∃ h, a = h + h ∧ OddNumber h) :
    EvenTimesEven a ∧ EvenTimesOdd a := by
  constructor
  · -- its half is not odd, so it is even, and the dyad measures `a` according to it
    obtain ⟨h, hh0, rfl⟩ := ha
    rcases even_or_odd hh0 with he | ho
    · exact ⟨2, h, ⟨1, Nat.one_pos, rfl⟩, he, by omega⟩
    · exact absurd ⟨h, rfl, ho⟩ hh
  · -- cut in half continually, we come to an odd number measuring `a` according to a
    -- number doubled from the unit; not the unit, `a` being even, and not to the dyad
    -- alone, else `a` would be doubled from a dyad
    rcases halve_continually (show 0 < a by have := ha.one_lt; omega) with
      ⟨k, hk⟩ | ⟨k, m, hk, hm, hm1⟩
    · exact absurd hk (hd k)
    · rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [show powers 1 2 0 (Fin.last 0) = 1 from rfl, Nat.one_mul] at hk
        exact (hm.2 (by rw [← hk]; exact ha)).elim
      · exact ⟨_, m, powers_two_even (Fin.last k) hk0, hm, hm1, hk⟩

end Elements.Book9
