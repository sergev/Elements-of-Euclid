import Elements.Book5.Prop09
import Elements.Book5.Prop10
import Elements.Book5.Prop11
import Elements.Book5.Prop13

namespace Elements.Book5

variable {M N : Type*} [Magnitude M] [Magnitude N]

/-- The first case: `A` greater than `C`. -/
theorem proposition_21_lemma {a b c : M} {d e f : N}
    (h₁ : Proportion a b e f) (h₂ : Proportion b c d e) (h : c < a) : f < d := by
  -- `A` has a greater ratio to `B` than `C` has to `B` [Prop. 5.8]
  have g₁ := (proposition_8 h b).1
  -- `A : B :: E : F`, so `E` has a greater ratio to `F` than `C` to `B` [Prop. 5.13]
  have g₂ := proposition_13 h₁.symm g₁
  -- inversely, `C : B :: E : D` [Prop. 5.7 corr.]; so `E : F` is greater than `E : D`
  -- [Prop. 5.13]
  have g₃ := proposition_13' g₂ (proposition_7_corollary h₂)
  -- and that to which the same has the greater ratio is lesser [Prop. 5.10]
  exact proposition_10' g₃

/--
If there are three magnitudes `A`, `B`, `C`, and as many others `D`, `E`, `F`, in the same
ratio taken two by two, and their proportion is perturbed, `A : B :: E : F` and
`B : C :: D : E`, then, via equality, if the first `A` is greater than the third `C`, the
fourth `D` is greater than the sixth `F`; if equal, equal; if less, less.
-/
theorem proposition_21 {a b c : M} {d e f : N}
    (h₁ : Proportion a b e f) (h₂ : Proportion b c d e) :
    (c < a → f < d) ∧ (a = c → d = f) ∧ (a < c → d < f) := by
  refine ⟨proposition_21_lemma h₁ h₂, fun hac => ?_, fun hac => ?_⟩
  · -- similarly, if `A` is equal to `C`: `A : B :: C : B` [Prop. 5.7], so
    -- `E : F :: E : D` [Props. 5.7 corr., 5.11], and `F` is equal to `D` [Prop. 5.9]
    have g₁ := proposition_11 h₁.symm (proposition_7 b hac).1
    exact (proposition_9' (proposition_11 g₁ (proposition_7_corollary h₂))).symm
  · -- and if `A` is less than `C`: `C : B :: E : D` and `B : A :: F : E`
    -- [Prop. 5.7 corr.]
    exact proposition_21_lemma (proposition_7_corollary h₂)
      (proposition_7_corollary h₁) hac
