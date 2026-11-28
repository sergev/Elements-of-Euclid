import Elements.Book5.Prop18
import Elements.Book5.Prop22

namespace Elements.Book5

variable {M N : Type*} [Magnitude M] [Magnitude N]

/--
If a first `AB` has to a second `C` the same ratio as a third `DE` to a fourth `F`, and a
fifth `BG` has to the second the same ratio as a sixth `EH` to the fourth, then the first
and the fifth together, `AG`, have to the second the same ratio as the third and the
sixth together, `DH`, to the fourth. `fourth` is a fourth proportional to `AG`, `GB`,
`DH`, for Prop. 5.18.
-/
theorem proposition_24 {a b e : M} {c d f : N}
    (h₁ : Proportion a b c d) (h₂ : Proportion e b f d)
    (fourth : ∃ x : N, Proportion (a + e) e (c + f) x) :
    Proportion (a + e) b (c + f) d := by
  -- inversely, `C : BG :: F : EH` [Prop. 5.7 corr.]; so via equality `AB : BG :: DE : EH`
  -- [Prop. 5.22]
  have g₁ := proposition_22' h₁ (proposition_7_corollary h₂)
  -- composed, `AG : GB :: DH : HE` [Prop. 5.18]
  -- Missed by Euclid: a fourth proportional exists.
  have g₂ := proposition_18 g₁ fourth
  -- and `BG : C :: EH : F`; so via equality `AG : C :: DH : F` [Prop. 5.22]
  exact proposition_22' g₂ h₂
