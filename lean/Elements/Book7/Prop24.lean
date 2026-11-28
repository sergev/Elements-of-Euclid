import Elements.Book7.Prop23

namespace Elements.Book7

/-- If `a` and `b` are prime to `c`, the number `b * a` made by `a` multiplying `b` is
prime to `c`. -/
theorem proposition_24 {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hac : PrimeTo a c) (hbc : PrimeTo b c) : PrimeTo c (b * a) := by
  -- if not, some number `e` measures `c` and `d = b * a`, `f` times
  intro e hec ⟨f, hf⟩
  have hd := Nat.mul_pos hb ha
  have he : 0 < e := Nat.pos_of_dvd_of_pos hec hc
  have hf0 : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; rw [Nat.mul_zero] at hf; omega)
  -- `c` and `a` are prime to one another, and `e` measures `c`: `a`, `e` are prime to
  -- one another [Prop. 7.23]
  have hae : PrimeTo e a := proposition_23 hac.symm hec
  -- `e` multiplying `f` makes `d`, as `a` multiplying `b` [Def. 7.15, Prop. 7.16]; so
  -- `e ∶ a ∷ b ∶ f` [Prop. 7.19]
  have h : e ∶ a ∷ b ∶ f := by
    rw [proposition_19 he ha hb hf0, hf, proposition_16 hf0 he]
  -- `a`, `e` are the least in their ratio [Prop. 7.21], and measure `b`, `f` as many
  -- times [Prop. 7.20]: `e` measures `b`
  obtain ⟨n, hn, -⟩ := proposition_20 hb hf0 he ha (proposition_21 he ha hae) h
  -- and `c`: but `b`, `c` are prime to one another
  exact hbc e ⟨n, hn⟩ hec

end Elements.Book7
