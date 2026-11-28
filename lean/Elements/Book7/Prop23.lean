import Elements.Book7.Prop22

namespace Elements.Book7

/-- If `a` and `b` are prime to one another, a number `c` measuring `a` is prime to
`b`. -/
theorem proposition_23 {a b c : ℕ} (h : PrimeTo a b) (hca : c ∣ a) : PrimeTo c b := by
  -- if not, some number `d` measures `c` and `b`
  intro d hdc hdb
  -- `d` measures `c`, and `c` measures `a`, so `d` measures `a`; and `b`
  exact h d (measures_trans hdc hca) hdb

end Elements.Book7
