import Elements.Book8.Lemmas

namespace Elements.Book8

open Elements.Book7

/--
If there are any multitude whatsoever of continuously proportional numbers `a 0`, …,
`a n`, and the outermost of them are prime to one another, then they are the least of
those having the same ratio as them. The proof does not use that they are continuously
proportional, so it is not a hypothesis.
-/
theorem proposition_1 {n : ℕ} {a : Fin (n + 1) → ℕ} (ha : ∀ i, 0 < a i)
    (h : PrimeTo (a 0) (a (Fin.last n))) : LeastSeq a := by
  -- if not, let `b` be less than `a`, each than each, in the same ratio as them
  intro b hb hab hlt
  -- via equality, as `a 0` is to the last of `a`, so `b 0` to the last of `b`
  -- [Prop. 7.14]
  have h14 := hab.extremes ha hb (Fin.last n)
  -- `a 0` and the last are prime, so the least [Prop. 7.21], and the least measure those
  -- in the same ratio, the leading the leading [Prop. 7.20]
  have hl := Elements.Book7.proposition_21 (ha 0) (ha _) h
  obtain ⟨k, hk, -⟩ :=
    Elements.Book7.proposition_20 (hb 0) (hb _) (ha 0) (ha _) hl h14.symm
  -- so `a 0` measures `b 0`, the greater the lesser: impossible
  exact not_measures_of_lt (hb 0) (hlt 0) ⟨k, hk⟩

end Elements.Book8
