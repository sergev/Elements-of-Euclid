import Elements.Book7.Prop21

namespace Elements.Book7

/-- The least numbers `a`, `b` of those having the same ratio as them are prime to one
another. -/
theorem proposition_22 {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h : Least a b) :
    PrimeTo a b := by
  -- if not, some number `c` measures them, `d` and `e` times
  intro c ⟨d, hd⟩ ⟨e, he⟩
  by_contra hc1
  have hc : 1 < c := by
    have := Nat.pos_of_ne_zero (by rintro rfl; rw [Nat.zero_mul] at hd; omega : c ≠ 0)
    omega
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; rw [Nat.mul_zero] at hd; omega)
  have he0 : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; rw [Nat.mul_zero] at he; omega)
  -- `c` has made `a` and `b` by multiplying `d` and `e` [Def. 7.15, Prop. 7.16]
  rw [proposition_16 hd0 (by omega)] at hd
  rw [proposition_16 he0 (by omega)] at he
  -- so as `d` is to `e`, so is `a` to `b` [Prop. 7.17]
  have h' := proposition_17 (by omega : 0 < c) hd0 he0
  rw [← hd, ← he] at h'
  -- `d`, `e` are less than `a`, `b`: impossible
  exact h d e hd0 he0 h' ⟨hd ▸ lt_mul hd0 hc, he ▸ lt_mul he0 hc⟩

end Elements.Book7
