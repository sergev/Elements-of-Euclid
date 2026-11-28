import Elements.Book9.Prop22

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/-- If any multitude of odd numbers are added together, and their multitude is odd, the
whole is odd. -/
theorem proposition_23 {n : ℕ} {a : Fin (n + 1) → ℕ} (ha : ∀ i, OddNumber (a i))
    (hn : OddNumber (n + 1)) : OddNumber (sum a) := by
  cases n with
  | zero => exact ha 0
  | succ k =>
    -- let the unit be taken from the last: the remainder is even, or nothing [Def. 7.7]
    obtain ⟨e, he⟩ := odd_iff.mp (ha (Fin.last (k + 1)))
    -- the rest, an even multitude, added together are even [Prop. 9.22]
    have hk : EvenNumber (k + 1) := by
      obtain ⟨j, hj⟩ := odd_iff.mp hn
      exact ⟨j, by omega, by omega⟩
    obtain ⟨s, -, hs⟩ := proposition_22 (a := fun i : Fin (k + 1) => a i.castSucc)
      (fun i => ha _) hk
    -- so the whole less the unit is even [Prop. 9.21], and the whole is odd [Def. 7.7]
    rw [sum_succ, hs, he]
    exact odd_iff.mpr ⟨s + e, by omega⟩

end Elements.Book9
