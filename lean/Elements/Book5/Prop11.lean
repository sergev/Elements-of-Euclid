import Elements.Book5.Magnitude

namespace Elements.Book5

variable {M N K : Type*} [Magnitude M] [Magnitude N] [Magnitude K]

/-- Ratios the same as the same ratio are the same: `A : B :: C : D :: E : F`. -/
theorem proposition_11 {a b : M} {c d : N} {e f : K}
    (h₁ : Proportion a b c d) (h₂ : Proportion c d e f) : Proportion a b e f where
  -- equal multiples `G`, `H`, `K` of `A`, `C`, `E`, and `L`, `M`, `N` of `B`, `D`, `F`:
  -- if `G` exceeds `L`, `H` exceeds `M`, and then `K` exceeds `N`, and conversely;
  -- and the same for equal and less [Def. 5.5]
  gt m n := (h₁.gt m n).trans (h₂.gt m n)
  eq m n := (h₁.eq m n).trans (h₂.eq m n)
  lt m n := (h₁.lt m n).trans (h₂.lt m n)
