import Elements.Book5.Prop14
import Elements.Book5.Prop15

namespace Elements.Book5

variable {M : Type*} [Magnitude M]

/--
If four magnitudes are proportional, `A : B :: C : D`, then they are also proportional
alternately, `A : C :: B : D`. All four are of one kind.
-/
theorem proposition_16 {a b c d : M} (h : Proportion a b c d) : Proportion a c b d := by
  -- let `E`, `F` be equal multiples of `A`, `B`, and `G`, `H` of `C`, `D`
  have key : ∀ m n : ℕ+, Proportion (m • a) (m • b) (n • c) (n • d) := by
    intro m n
    -- `A : B :: E : F` [Prop. 5.15], so `C : D :: E : F` [Prop. 5.11]
    have h₁ := proposition_11 h.symm (proposition_15 a b m)
    -- `C : D :: G : H` [Prop. 5.15], so `E : F :: G : H` [Prop. 5.11]
    exact proposition_11 h₁.symm (proposition_15 c d n)
  -- if `E` exceeds `G`, `F` exceeds `H`; if equal, equal; if less, less [Prop. 5.14]
  apply Proportion.of_imp <;> intro m n h₁
  · exact (proposition_14 (key m n)).1 h₁
  · exact (proposition_14 (key m n)).2.1 h₁
  · exact (proposition_14 (key m n)).2.2 h₁
