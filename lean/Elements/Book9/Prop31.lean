import Elements.Book9.Prop30

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/-- An even number `e` multiplied by any number `k` makes an even number: `e` taken `k`
times, even numbers added together [Def. 7.15, Prop. 9.21]. -/
theorem EvenNumber.mul {e k : ℕ} (he : EvenNumber e) (hk : 0 < k) :
    EvenNumber (e * k) := by
  rw [mul_eq_sum e hk]
  exact proposition_21 fun _ => he

/-- A number measuring an odd number is odd: an even number measures only even numbers.
-/
theorem OddNumber.of_measures {a d : ℕ} (ha : OddNumber a) (hd : d ∣ a) :
    OddNumber d := by
  obtain ⟨m, hm⟩ := hd
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => by
    have := ha.1; rw [hm, h, Nat.mul_zero] at this; omega
  have hd0 : 0 < d := Nat.pos_of_ne_zero fun h => by
    have := ha.1; rw [hm, h, Nat.zero_mul] at this; omega
  rcases even_or_odd hd0 with h | h
  · exact absurd (hm ▸ h.mul hm0) ha.2
  · exact h

/-- If an odd number `a` is prime to some number `b`, it is also prime to its double. -/
theorem proposition_31 {a b : ℕ} (ha : OddNumber a) (hb : 0 < b) (h : PrimeTo a b) :
    PrimeTo a (b + b) := by
  -- if not, some `d` measures them
  intro d hda hdb
  -- `a` is odd, so `d` is odd [Prop. 9.21] -- Missed by Euclid.
  have hd := ha.of_measures hda
  -- `d`, odd, measures the even `b + b`, so it measures its half `b` [Prop. 9.30]
  have := proposition_30 hd hb hdb
  -- and it measures `a`: `a` and `b` are prime to one another
  exact h d hda this

end Elements.Book9
