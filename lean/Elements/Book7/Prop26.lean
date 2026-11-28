import Elements.Book7.Prop25

namespace Elements.Book7

/-- If `a` and `b` are both prime to each of `c` and `d`, the numbers `b * a` and `d * c`
they make are prime to one another. -/
theorem proposition_26 {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hac : PrimeTo a c) (hbc : PrimeTo b c) (had : PrimeTo a d) (hbd : PrimeTo b d) :
    PrimeTo (b * a) (d * c) := by
  -- `a` and `b` are prime to `c`, so is `e = b * a` [Prop. 7.24]; and to `d`
  have hec := proposition_24 ha hb hc hac hbc
  have hed := proposition_24 ha hb hd had hbd
  -- `c` and `d` are prime to `e`, so is `d * c` [Prop. 7.24]
  exact proposition_24 hc hd (Nat.mul_pos hb ha) hec hed

end Elements.Book7
