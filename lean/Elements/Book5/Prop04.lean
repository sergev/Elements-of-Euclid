import Elements.Book5.Prop03

namespace Elements.Book5

open Magnitude

variable {M N : Type*} [Magnitude M] [Magnitude N]

/--
If `A : B :: C : D`, then equal multiples `E`, `F` of the first and the third have the
same ratio to equal multiples `G`, `H` of the second and the fourth: `E : G :: F : H`.
-/
theorem proposition_4 {a b : M} {c d : N} (h : Proportion a b c d) (m n : ℕ+) :
    Proportion (m • a) (n • b) (m • c) (n • d) := by
  -- let equal multiples `K`, `L` be taken of `E`, `F`, and `M`, `N` of `G`, `H`;
  -- `K`, `L` are equal multiples of `A`, `C`, and `M`, `N` of `B`, `D` [Prop. 5.3]
  refine ⟨fun k l => ?_, fun k l => ?_, fun k l => ?_⟩ <;>
    rw [proposition_3, proposition_3, proposition_3, proposition_3]
  -- `K`, `L` exceed together, are equal together, are less together [Def. 5.5]
  · exact h.gt _ _
  · exact h.eq _ _
  · exact h.lt _ _
