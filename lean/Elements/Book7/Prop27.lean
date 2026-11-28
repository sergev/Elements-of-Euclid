import Elements.Book7.Prop26

namespace Elements.Book7

/--
If `a` and `b` are prime to one another, and each makes some number by multiplying itself,
`a * a` and `b * b`, these are prime to one another; and so are the numbers they make
multiplying these, `a * a * a` and `b * b * b`.
-/
theorem proposition_27 {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h : PrimeTo a b) :
    PrimeTo (a * a) (b * b) ∧ PrimeTo (a * a * a) (b * b * b) := by
  have hc := Nat.mul_pos ha ha
  have he := Nat.mul_pos hb hb
  -- `a * a` and `b` are prime to one another [Prop. 7.25]; so `a * a` and `b * b`
  have hcb := proposition_25 ha hb h
  have hce := proposition_25 hb hc hcb
  -- and `a` and `b * b` [Prop. 7.25]
  have hae := proposition_25 hb ha h.symm
  -- `a` and `a * a` are each prime to `b` and `b * b`; so are the numbers they make
  -- [Prop. 7.26]
  exact ⟨hce, proposition_26 ha hc hb he h hcb.symm hae hce⟩

end Elements.Book7
