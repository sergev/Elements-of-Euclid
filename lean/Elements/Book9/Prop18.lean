import Elements.Book9.Prop17

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/--
For two given numbers `a`, `b`, to investigate whether a third proportional can be found:
it can exactly when `a` measures `b` multiplying itself.

Euclid first sets aside numbers prime to one another, for which there is none
[Prop. 9.16]; the criterion covers them (`a` prime to `b` measures `b * b` only if it is
the unit).
-/
theorem proposition_18 {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (∃ d, 0 < d ∧ a ∶ b ∷ b ∶ d) ↔ a ∣ b * b := by
  constructor
  · -- if found, `a` multiplying `d` makes `b * b` [Prop. 7.19], so `a` measures it
    rintro ⟨d, hd, h⟩
    rw [Elements.Book7.proposition_19 ha hb hb hd] at h
    exact ⟨d, by rw [← h, Elements.Book7.proposition_16 ha hd]⟩
  · -- if `a` measures `b * b` according to `d`, then as `a` is to `b`, so `b` is to `d`
    -- [Prop. 7.19]
    rintro ⟨d, hd⟩
    have hd0 : 0 < d := Nat.pos_of_ne_zero fun h => by
      have := Nat.mul_pos hb hb; rw [hd, h, Nat.mul_zero] at this; omega
    refine ⟨d, hd0, ?_⟩
    rw [Elements.Book7.proposition_19 ha hb hb hd0, Elements.Book7.proposition_16 ha hd0,
      hd]

end Elements.Book9
