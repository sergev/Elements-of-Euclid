import Elements.Book8.Prop06

namespace Elements.Book8

open Elements.Book7

/-- If there are any multitude whatsoever of continuously proportional numbers, and the
first measures the last, it will also measure the second. -/
theorem proposition_7 {n : ℕ} {a : Fin (n + 1) → ℕ} (ha : ∀ i, 0 < a i)
    (hc : Continued a) (h : a 0 ∣ a (Fin.last n)) : a 0 ∣ a 1 := by
  rcases n with _ | n
  · -- one number alone: the first is the second
    exact measures_self _
  · -- if `a 0` does not measure `a 1`, no other measures any other [Prop. 8.6]; but `a 0`
    -- measures the last
    by_contra h01
    exact proposition_6 ha hc h01 0 (Fin.last _) (Fin.pos_iff_ne_zero.mpr (by simp)) h

end Elements.Book8
