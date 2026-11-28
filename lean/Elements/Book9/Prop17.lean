import Elements.Book9.Prop16

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/-- If any multitude of numbers `a 0`, …, `a n` are continuously proportional, and the
outermost are prime to one another, there is no `e` such that as the first is to the
second, so the last is to `e`. The first is a number, greater than the unit. -/
theorem proposition_17 {n : ℕ} {a : Fin (n + 1) → ℕ} (ha : ∀ i, 0 < a i)
    (h1 : 1 < a 0) (hcon : Continued a) (h : PrimeTo (a 0) (a (Fin.last n))) :
    ¬ ∃ e, 0 < e ∧ a 0 ∶ a 1 ∷ a (Fin.last n) ∶ e := by
  rintro ⟨e, he, hae⟩
  -- alternately, as `a 0` is to the last, so `a 1` to `e` [Prop. 7.13]
  have h13 := Elements.Book7.proposition_13 (ha 0) (ha 1) (ha _) he hae
  -- `a 0` and the last are the least [Prop. 7.21], so `a 0` measures `a 1` [Prop. 7.20]
  obtain ⟨m, hm, -⟩ := Elements.Book7.proposition_20 (ha 1) he (ha 0) (ha _)
    (Elements.Book7.proposition_21 (ha 0) (ha _) h) h13
  -- each measures the next [Def. 7.20], so `a 0` measures all, and the last
  have hall : ∀ i, a 0 ∣ a i := by
    intro i
    induction i using Fin.induction with
    | zero => exact measures_self _
    | succ i ih =>
      exact measures_trans ih (measures_of_proportion (ha 0) (ha 1) (ha _) (ha _)
        (hcon i).symm ⟨m, hm⟩)
  -- `a 0` measures itself and the last, prime to one another
  have := h _ (measures_self _) (hall _)
  omega

end Elements.Book9
