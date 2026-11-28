import Elements.Book5.Magnitude

namespace Elements.Book5

variable {M N K : Type*} [Magnitude M] [Magnitude N] [Magnitude K]

/--
If `A : B :: C : D`, and `C : D` is greater than `E : F`, then `A : B` is greater than
`E : F`.
-/
theorem proposition_13 {a b : M} {c d : N} {e f : K}
    (h₁ : Proportion a b c d) (h₂ : GreaterRatio c d e f) : GreaterRatio a b e f := by
  -- let `G`, `H` be equal multiples of `C`, `E`, and `K`, `L` of `D`, `F`, with `G`
  -- exceeding `K`, and `H` not exceeding `L` [Def. 5.7]
  obtain ⟨m, n, hGK, hHL⟩ := h₂
  -- let `M`, `N` be the same multiples of `A`, `B`: `M` exceeds `N`, as `G` exceeds `K`
  -- [Def. 5.5], and `H` does not exceed `L` [Def. 5.7]
  exact ⟨m, n, (h₁.gt m n).mpr hGK, hHL⟩

/--
The same with the greater ratio first: if `A : B` is greater than `C : D`, and
`C : D :: E : F`, then `A : B` is greater than `E : F`. Euclid cites Prop. 5.13 for it.
-/
theorem proposition_13' {a b : M} {c d : N} {e f : K}
    (h₁ : GreaterRatio a b c d) (h₂ : Proportion c d e f) : GreaterRatio a b e f := by
  obtain ⟨m, n, h, h'⟩ := h₁
  exact ⟨m, n, h, fun h'' => h' ((h₂.gt m n).mpr h'')⟩
