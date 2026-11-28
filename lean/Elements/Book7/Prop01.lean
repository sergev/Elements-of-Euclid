import Elements.Book7.Lemmas

namespace Elements.Book7

/-- Euclid's argument: a number `e` measuring `a` and `b` measures each remainder, as it
measures the whole and the part taken away, and so the last. -/
theorem measures_remainder {e a b : ℕ} (ha : e ∣ a) (hb : e ∣ b) : e ∣ remainder a b := by
  fun_induction remainder a b with
  | case1 => exact hb
  | case2 => exact ha
  -- `e` measures the whole `b` and `a` taken away, so the remainder
  | case3 a b _ _ _ ih => exact ih ha (measures_sub hb ha)
  | case4 a b _ _ _ _ ih => exact ih (measures_sub ha hb) hb
  | case5 => exact ha

/--
Two unequal numbers `a`, `b`, the lesser subtracted continually, in turn, from the
greater: if the remainder never measures the number before it until a unit remains, then
`a` and `b` are prime to one another. (That they are numbers is not needed.)
-/
theorem proposition_1 {a b : ℕ} (h : remainder a b = 1) : PrimeTo a b := by
  -- if some number `e` measures them
  intro e hea heb
  -- `e` measures the remaining unit, so it is not a number
  have he : e ∣ 1 := h ▸ measures_remainder hea heb
  exact Nat.eq_one_of_dvd_one he

end Elements.Book7
