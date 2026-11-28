import Elements.Book7.Prop24

namespace Elements.Book7

/-- If `a` and `b` are prime to one another, the number `a * a` made by `a` multiplying
itself is prime to `b`. -/
theorem proposition_25 {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h : PrimeTo a b) :
    PrimeTo b (a * a) := by
  -- let `d` be equal to `a`: `d` and `a` are each prime to `b`, and so is the number
  -- they make [Prop. 7.24]
  exact proposition_24 ha ha hb h h

end Elements.Book7
