import Elements.Book9.Prop18

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/--
For three given numbers `a`, `b`, `c`, to investigate when a fourth proportional can be
found: it can exactly when `a` measures `b` multiplying `c`.

Euclid's case analysis is defective (Fitzpatrick's note). He takes four cases: `a`, `b`,
`c` continuously proportional or not, and the outermost prime to one another or not.
- Continuously proportional, outermost prime: none [Prop. 9.17]. Correct.
- Not continuously proportional, outermost prime: none, he says. His proof assumes a
  fifth `e` with `b ∶ c ∷ d ∶ e`, which need not exist, and the claim is false: `2`, `4`,
  `3` have the fourth proportional `6`.
- The other two cases: one can be found exactly when `a` measures `c * b`, by 7.19.
  Correct, and this is the criterion in every case.
The statement is the criterion, proved as his last cases are.
-/
theorem proposition_19 {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (∃ e, 0 < e ∧ a ∶ b ∷ c ∶ e) ↔ a ∣ c * b := by
  constructor
  · -- if found, `a` multiplying `e` makes `c * b` [Prop. 7.19], so `a` measures it
    rintro ⟨e, he, h⟩
    rw [Elements.Book7.proposition_19 ha hb hc he] at h
    exact ⟨e, by rw [← h, Elements.Book7.proposition_16 ha he]⟩
  · -- if `a` measures `d = c * b` according to `e`, then `a` multiplying `e` makes what
    -- `b` multiplying `c` makes, and as `a` is to `b`, so `c` is to `e` [Prop. 7.19]
    rintro ⟨e, he⟩
    have he0 : 0 < e := Nat.pos_of_ne_zero fun h => by
      have := Nat.mul_pos hc hb; rw [he, h, Nat.mul_zero] at this; omega
    refine ⟨e, he0, ?_⟩
    rw [Elements.Book7.proposition_19 ha hb hc he0, Elements.Book7.proposition_16 ha he0,
      he]

/-- Euclid's second case is false: `2`, `4`, `3` are not continuously proportional, the
outermost are prime to one another, and `6` is a fourth proportional. -/
theorem proposition_19_counterexample :
    ¬ (2 ∶ 4 ∷ 4 ∶ 3) ∧ PrimeTo 2 3 ∧ 2 ∶ 4 ∷ 3 ∶ 6 := by
  refine ⟨fun h => ?_, fun d h2 h3 => ?_, ?_⟩
  · rw [Elements.Book7.proposition_19 (by omega) (by omega) (by omega) (by omega)] at h
    omega
  · have := le_of_measures (by omega) h2
    obtain ⟨k, hk⟩ := h3
    obtain ⟨l, hl⟩ := h2
    rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2) with rfl | rfl | rfl <;> omega
  · rw [Elements.Book7.proposition_19 (by omega) (by omega) (by omega) (by omega)]

end Elements.Book9
