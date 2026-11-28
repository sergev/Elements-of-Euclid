import Elements.Book5.Prop16
import Elements.Book5.Prop21

namespace Elements.Book5

variable {M : Type*} [Magnitude M]

/--
If there are three magnitudes `A`, `B`, `C`, and as many others `D`, `E`, `F`, in the same
ratio taken two by two, and their proportion is perturbed, `A : B :: E : F` and
`B : C :: D : E`, then via equality `A : C :: D : F`. The proof alternates `B : C ::
D : E`, so all six are of one kind.
-/
theorem proposition_23 {a b c d e f : M}
    (h₁ : Proportion a b e f) (h₂ : Proportion b c d e) : Proportion a c d f := by
  -- let `G`, `H`, `K` be equal multiples `m` of `A`, `B`, `D`, and `L`, `M`, `N` others
  -- `n` of `C`, `E`, `F`
  have key : ∀ m n : ℕ+,
      (n • c < m • a → n • f < m • d) ∧ (m • a = n • c → m • d = n • f) ∧
        (m • a < n • c → m • d < n • f) := by
    intro m n
    -- `A : B :: G : H` and `E : F :: M : N` [Prop. 5.15]; so `G : H :: M : N`
    -- [Prop. 5.11]
    have g₁ := proposition_11 (proposition_11 (proposition_15 a b m).symm h₁)
      (proposition_15 e f n)
    -- alternately, `B : D :: C : E` [Prop. 5.16]; `B : D :: H : K` [Prop. 5.15], so
    -- `H : K :: C : E` [Prop. 5.11]
    have g₂ := proposition_11 (proposition_15 b d m).symm (proposition_16 h₂)
    -- `C : E :: L : M` [Prop. 5.15], so `H : K :: L : M` [Prop. 5.11]
    have g₃ := proposition_11 g₂ (proposition_15 c e n)
    -- alternately, `H : L :: K : M` [Prop. 5.16]; and `G : H :: M : N`; so via equality,
    -- perturbed, if `G` exceeds `L`, `K` exceeds `N`; if equal, equal; if less, less
    -- [Prop. 5.21]
    exact proposition_21 g₁ (proposition_16 g₃)
  -- so `A : C :: D : F` [Def. 5.5]
  exact Proportion.of_imp (fun m n => (key m n).1) (fun m n => (key m n).2.1)
    (fun m n => (key m n).2.2)
