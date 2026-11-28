import Elements.Book9.Prop29

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/-- If an odd number `a` measures an even number `h + h`, it also measures its half
`h`. -/
theorem proposition_30 {a h : ℕ} (ha : OddNumber a) (hh : 0 < h) (hab : a ∣ h + h) :
    a ∣ h := by
  -- let `a` measure `b` according to `c`
  obtain ⟨c, hc⟩ := hab
  have hc0 : 0 < c := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.mul_zero] at hc; omega
  -- `c` is not odd: else `b` is made of odd numbers, an odd multitude, and is odd
  -- [Prop. 9.23]
  have hce : EvenNumber c := by
    rcases even_or_odd hc0 with h' | h'
    · exact h'
    · exfalso
      have hodd : OddNumber (a * c) := by
        rw [mul_eq_sum a hc0]
        exact proposition_23 (fun _ => ha) (by rwa [show c - 1 + 1 = c by omega])
      rw [← hc] at hodd
      exact hodd.2 ⟨h, hh, rfl⟩
  -- so `a` measures `b` an even number of times, and its half half as many
  obtain ⟨k, -, rfl⟩ := hce
  exact ⟨k, by rw [Nat.mul_add] at hc; omega⟩

end Elements.Book9
