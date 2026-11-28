import Elements.Book8.Prop02

namespace Elements.Book8

open Elements.Book7

/-- If there are any multitude whatsoever of continuously proportional numbers which are
the least of those having the same ratio as them, the outermost of them are prime to one
another. -/
theorem proposition_3 {n : ℕ} {a : Fin (n + 1) → ℕ} (ha : ∀ i, 0 < a i)
    (hc : Continued a) (hl : LeastSeq a) : PrimeTo (a 0) (a (Fin.last n)) := by
  -- let `e`, `f` be the least in the ratio of `a 0` to `a 1` [Prop. 7.33], and the
  -- least numbers in that ratio, as many as `a`, be taken [Prop. 8.2]: being the least
  -- in the same ratios, they are `a`, each to each
  obtain ⟨e, f, he, hf, hef, rfl⟩ := eq_powers ha hc hl
  -- `e`, `f` are prime to one another [Prop. 7.22], and so are the outermost
  -- [Prop. 7.27]
  exact powers_primeTo he hf (Elements.Book7.proposition_22 he hf hef) n

end Elements.Book8
