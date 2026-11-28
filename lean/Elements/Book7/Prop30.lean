import Elements.Book7.Prop29

namespace Elements.Book7

/-- If `a` and `b` make `b * a` by multiplying one another, and a prime number `d`
measures it, then `d` measures one of `a` and `b`. -/
theorem proposition_30 {a b d : ℕ} (ha : 0 < a) (hb : 0 < b) (hd : PrimeNumber d)
    (h : d ∣ b * a) : d ∣ a ∨ d ∣ b := by
  -- let `d` not measure `a`
  by_cases hda : d ∣ a
  · exact Or.inl hda
  right
  -- `a` and `d` are prime to one another [Prop. 7.29]
  have had := proposition_29 hd hda
  -- `d` measures `b * a`, `e` times
  obtain ⟨e, he⟩ := h
  have hd0 : 0 < d := by have := hd.1; omega
  have he0 : 0 < e := Nat.pos_of_ne_zero (by
    rintro rfl
    rw [Nat.mul_zero] at he
    exact absurd he (Nat.mul_pos hb ha).ne')
  -- `d` made `b * a` by multiplying `e` [Def. 7.15, Prop. 7.16], as `a` by multiplying
  -- `b`: so `d ∶ a ∷ b ∶ e` [Prop. 7.19]
  have h' : d ∶ a ∷ b ∶ e := by
    rw [proposition_19 hd0 ha hb he0, he, proposition_16 he0 hd0]
  -- `d`, `a` are the least in their ratio [Prop. 7.21], and measure `b`, `e` as many
  -- times [Prop. 7.20]: `d` measures `b`
  obtain ⟨n, hn, -⟩ := proposition_20 hb he0 hd0 ha (proposition_21 hd0 ha had.symm) h'
  exact ⟨n, hn⟩

end Elements.Book7
