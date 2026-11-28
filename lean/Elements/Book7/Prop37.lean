import Elements.Book7.Prop36

namespace Elements.Book7

/-- If `b` measures `a`, then `a` has a part `c` called the same as `b`: `c` is the `b`th
part of `a`. -/
theorem proposition_37 {a b : ℕ} (hb : 1 < b) (h : b ∣ a) : ∃ c, PartOf c a b := by
  -- as many times as `b` measures `a`, so many units are in `c`
  obtain ⟨c, hc⟩ := h
  -- the unit measures `c` as many times as `b` measures `a`; alternately, the unit
  -- measures `b` as many times as `c` measures `a` [Prop. 7.15]
  rcases Nat.eq_zero_or_pos c with rfl | hc0
  · exact ⟨0, hb, by rw [hc, Nat.mul_zero, Nat.zero_mul]⟩
  obtain ⟨m, hm, ha⟩ := proposition_15 (by omega) hc0 (Nat.one_mul c).symm hc
  rw [Nat.one_mul] at hm
  -- so `c` is the same part of `a` as the unit of `b`, called the same as `b`
  exact ⟨c, hb, hm ▸ ha⟩

end Elements.Book7
