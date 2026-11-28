import Elements.Book7.Prop27

namespace Elements.Book7

/-- If `a` and `b` are prime to one another, their sum `a + b` is prime to each of
them. -/
theorem proposition_28 {a b : ℕ} (h : PrimeTo a b) :
    PrimeTo (a + b) a ∧ PrimeTo (a + b) b := by
  constructor
  · -- if not, some number `d` measures `a + b` and `a`, so the remainder `b`
    intro d hs ha
    have hb := measures_sub hs ha
    rw [Nat.add_sub_cancel_left] at hb
    -- `d` measures `a` and `b`, which are prime to one another
    exact h d ha hb
  · intro d hs hb
    have ha := measures_sub hs hb
    rw [Nat.add_sub_cancel] at ha
    exact h d ha hb

/-- If the sum `a + b` is prime to one of them, `a`, then `a` and `b` are prime to one
another. -/
theorem proposition_28' {a b : ℕ} (h : PrimeTo (a + b) a) : PrimeTo a b := by
  -- if not, some number `d` measures `a` and `b`, so the whole `a + b`
  intro d ha hb
  -- `d` measures `a + b` and `a`, which are prime to one another
  exact h d (measures_add ha hb) ha

end Elements.Book7
