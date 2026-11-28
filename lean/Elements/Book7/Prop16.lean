import Elements.Book7.Prop15

namespace Elements.Book7

/-- If `a` multiplying `b` makes `b * a`, and `b` multiplying `a` makes `a * b`, they are
equal. From here on Mathlib's `Nat.mul_comm` is this proposition. -/
theorem proposition_16 {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : b * a = a * b := by
  -- `b` measures `b * a` according to the units in `a` [Def. 7.15], and the unit measures
  -- `a` according to the units in it; alternately, the unit measures `b` as many times as
  -- `a` measures `b * a` [Prop. 7.15]
  obtain ⟨m, hm, h⟩ := proposition_15 (e := b * a) hb ha (Nat.one_mul a).symm rfl
  rw [Nat.one_mul] at hm
  -- and `a` measures `a * b` according to the units in `b`: `a` measures both as many
  -- times
  rw [h, hm]

end Elements.Book7
