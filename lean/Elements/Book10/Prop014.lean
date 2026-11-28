import Elements.Book10.Prop013

namespace Elements.Book10

open Elements.Book5

/--
If four lines are proportional, `a ∶ b ∷ c ∶ d`, and the square on `a` exceeds the square
on `b` by the square on `e`, and the square on `c` that on `d` by the square on `f`, then
`a` and `e` are commensurable in length exactly when `c` and `f` are.
-/
theorem proposition_14 {a b c d e f : Length} (h : Proportion a b c d)
    (he : sq b + sq e = sq a) (hf : sq d + sq f = sq c) :
    (Commensurable a e → Commensurable c f) ∧
      (¬ Commensurable a e → ¬ Commensurable c f) := by
  -- as the square on `a` is to the square on `b`, so the square on `c` to that on `d`
  -- [Prop. 6.22]
  have h₁ := proportion_sq.mp h
  -- that is, the squares on `e` and `b` to the square on `b`, as the squares on `f` and
  -- `d` to the square on `d`; via separation, as the square on `e` is to the square on
  -- `b`, so the square on `f` to that on `d` [Prop. 5.17]
  rw [← he, ← hf, add_comm (sq b), add_comm (sq d)] at h₁
  have h₂ := Elements.Book5.proposition_17 h₁
  -- so as `e` is to `b`, so `f` to `d` [Prop. 6.22]; inversely [Prop. 5.7 corr.]
  have h₃ := Elements.Book5.proposition_7_corollary (proportion_sq.mpr h₂)
  -- via equality, as `a` is to `e`, so `c` to `f` [Prop. 5.22]
  have h₄ := Elements.Book5.proposition_22' h h₃
  -- [Prop. 10.11]
  exact proposition_11 h₄ Length.divisible Length.divisible

/-- 10.14, with the excess as in Defs. II: if `a ∶ b ∷ c ∶ d`, and the square on `a`
exceeds the square on `b` by the square on a line commensurable (incommensurable) with
`a`, so the square on `c` that on `d`, by the square on a line commensurable
(incommensurable) with `c`. -/
theorem proposition_14' {a b c d : Length} (h : Proportion a b c d) :
    (ExceedsComm a b → ExceedsComm c d) ∧ (ExceedsIncomm a b → ExceedsIncomm c d) := by
  -- the square on `c` exceeds that on `d`, by the square on some `f` [Prop. 10.13 lemma]:
  -- `a` is greater than `b`, so `c` than `d` [Props. 5.16, 5.14]
  have hf : ∀ e, sq b + sq e = sq a → ∃ f, sq d + sq f = sq c := fun e he => by
    have hba : b < a := sq_lt_sq.mp (he ▸ Magnitude.lt_add _ _)
    exact Length.exceeds
      ((Elements.Book5.proposition_14 (Elements.Book5.proposition_16 h)).1 hba)
  constructor
  · rintro ⟨e, he, hea⟩
    obtain ⟨f, hf⟩ := hf e he
    exact ⟨f, hf, ((proposition_14 h he hf).1 hea.symm).symm⟩
  · rintro ⟨e, he, hea⟩
    obtain ⟨f, hf⟩ := hf e he
    exact ⟨f, hf, fun hfc =>
      (proposition_14 h he hf).2 (fun hae => hea hae.symm) hfc.symm⟩

end Elements.Book10
