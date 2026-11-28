import Elements.Book5.Prop09
import Elements.Book5.Prop10
import Elements.Book5.Prop11
import Elements.Book5.Prop13

namespace Elements.Book5

variable {M N : Type*} [Magnitude M] [Magnitude N]

/-- The first case: `A` greater than `C`. -/
theorem proposition_20_lemma {a b c : M} {d e f : N}
    (h₁ : Proportion a b d e) (h₂ : Proportion b c e f) (h : c < a) : f < d := by
  -- `A` has a greater ratio to `B` than `C` has to `B` [Prop. 5.8]
  have g₁ := (proposition_8 h b).1
  -- `A : B :: D : E`, so `D` has a greater ratio to `E` than `C` to `B` [Prop. 5.13]
  have g₂ := proposition_13 h₁.symm g₁
  -- inversely, `C : B :: F : E` [Prop. 5.7 corr.]; so `D : E` is greater than `F : E`
  -- [Prop. 5.13]
  have g₃ := proposition_13' g₂ (proposition_7_corollary h₂)
  -- and that which has the greater ratio to the same is greater [Prop. 5.10]
  exact proposition_10 g₃

/--
If there are three magnitudes `A`, `B`, `C`, and as many others `D`, `E`, `F`, in the same
ratio taken two by two, `A : B :: D : E` and `B : C :: E : F`, then, via equality, if the
first `A` is greater than the third `C`, the fourth `D` is greater than the sixth `F`; if
equal, equal; if less, less.
-/
theorem proposition_20 {a b c : M} {d e f : N}
    (h₁ : Proportion a b d e) (h₂ : Proportion b c e f) :
    (c < a → f < d) ∧ (a = c → d = f) ∧ (a < c → d < f) := by
  refine ⟨proposition_20_lemma h₁ h₂, fun hac => ?_, fun hac => ?_⟩
  · -- similarly, if `A` is equal to `C`: `A : B :: C : B` [Prop. 5.7], so
    -- `D : E :: F : E` [Props. 5.7 corr., 5.11], and `D` is equal to `F` [Prop. 5.9]
    have g₁ := proposition_11 h₁.symm (proposition_7 b hac).1
    exact proposition_9 (proposition_11 g₁ (proposition_7_corollary h₂))
  · -- and if `A` is less than `C`: `C : B :: F : E` and `B : A :: E : D`
    -- [Prop. 5.7 corr.]
    exact proposition_20_lemma (proposition_7_corollary h₂)
      (proposition_7_corollary h₁) hac
