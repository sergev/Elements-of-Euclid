import Elements.Book8.Prop19

namespace Elements.Book8

open Elements.Book7

/-- Euclid's construction in 8.20, with `a ∶ e ∷ e ∶ b`: `a = p * q`, `e = r * q`,
`b = r * s`, with `p`, `r` the least in the ratio of `a` to `e`, and `p ∶ q ∷ r ∶ s`. -/
theorem plane_of_mean {a e b : ℕ} (ha : 0 < a) (he : 0 < e) (hb : 0 < b)
    (h : a ∶ e ∷ e ∶ b) :
    ∃ p q r s, 0 < p ∧ 0 < q ∧ 0 < r ∧ 0 < s ∧ a = p * q ∧ e = r * q ∧ b = r * s ∧
      p ∶ q ∷ r ∶ s ∧ p ∶ r ∷ a ∶ e := by
  -- let the least numbers `p`, `r` having the same ratio as `a` and `e` be taken
  -- [Prop. 7.33]
  obtain ⟨p, r, hp, hr, hpr, hl⟩ := Elements.Book7.proposition_33' ha he
  -- `p` measures `a` as many times, `q`, as `r` measures `e` [Prop. 7.20]: `q` has made
  -- `a` by multiplying `p`. And so `q` has made `e` by multiplying `r`: Euclid takes `q`
  -- from `p` and `a` alone, and does not show it. -- Missed by Euclid.
  obtain ⟨q, rfl, rfl⟩ := Elements.Book7.proposition_20 ha he hp hr hl hpr
  -- `p`, `r` are the least having the same ratio as `e` and `b`, so `p` measures `e` as
  -- many times as `r` measures `b`, `s` times [Prop. 7.20]
  have hpr' : p ∶ r ∷ r * q ∶ b := proportion_trans hp hr ha he hpr h
  obtain ⟨s, hs, rfl⟩ := Elements.Book7.proposition_20 he hb hp hr hl hpr'
  have hq : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; rw [Nat.mul_zero] at ha; omega)
  have hs0 : 0 < s := Nat.pos_of_ne_zero (by rintro rfl; rw [Nat.mul_zero] at hb; omega)
  refine ⟨p, q, r, s, hp, hq, hr, hs0, rfl, rfl, rfl, ?_, hpr⟩
  -- (that `p ∶ r ∷ p * q ∶ r * q` is the hypothesis, `hpr`: Euclid shows it again, by
  -- Prop. 7.17; it is not needed.) `q`, `s` multiplying `r` make `r * q`, `r * s`: as `q`
  -- is to `s`, so they [Prop. 7.18], and so `p` to `r`
  have hqs : q ∶ s ∷ p ∶ r := proportion_trans hq hs0 he hb
    (Elements.Book7.proposition_18 hq hs0 hr) hpr'.symm
  -- alternately, as `p` is to `q`, so `r` to `s` [Prop. 7.13]
  exact Elements.Book7.proposition_13 hp hr hq hs0 hqs.symm

/--
If one number falls between two numbers in mean proportion, the numbers are similar plane
numbers: `p * q` and `r * s` with `p ∶ q ∷ r ∶ s` (Def. 7.21).

The sides may be the unit, and then the numbers are not plane (Def. 7.16): one number,
`4`, falls between `2` and `8`, but `2` is prime. Euclid does not notice; the statement
is for sides that may be the unit.
-/
theorem proposition_20 {a b : ℕ} (h : FallBetween 1 a b) :
    ∃ p q r s, 0 < p ∧ 0 < q ∧ 0 < r ∧ 0 < s ∧ a = p * q ∧ b = r * s ∧ p ∶ q ∷ r ∶ s := by
  obtain ⟨ha, hb, e, he, hae⟩ := h.one
  obtain ⟨p, q, r, s, hp, hq, hr, hs, rfl, -, rfl, h, -⟩ := plane_of_mean ha he hb hae
  exact ⟨p, q, r, s, hp, hq, hr, hs, rfl, rfl, h⟩

end Elements.Book8
