import Elements.Book7.Prop06

namespace Elements.Book7

/-- If `a` is that part of `b` that `e` taken away is of `f` taken away, then the
remainder `a - e` is the same part of the remainder `b - f`. -/
theorem proposition_7 {a b e f n : ℕ} (h₁ : PartOf a b n) (h₂ : PartOf e f n)
    (hea : e ≤ a) : PartOf (a - e) (b - f) n := by
  obtain ⟨hn, rfl⟩ := h₁
  obtain ⟨-, rfl⟩ := h₂
  -- let `g` be `a - e` taken `n` times: `g` and `f` are `a` taken `n` times [Prop. 7.5]
  have h := (proposition_5 (a := e) (d := a - e) ⟨hn, rfl⟩ ⟨hn, rfl⟩).2
  rw [Nat.add_sub_cancel' hea] at h
  -- so `g` and `f` are `b`; take `f` away: `g` is the remainder
  exact ⟨hn, by omega⟩

end Elements.Book7
