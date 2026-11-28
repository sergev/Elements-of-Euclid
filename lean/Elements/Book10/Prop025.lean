import Elements.Book10.Prop024

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- The rectangle contained by medial lines commensurable in square only is either
rational or medial. -/
theorem proposition_25 {x y : Length} (hx : Medial ρ x) (hy : Medial ρ y)
    (h : InSquareOnly x y) : RationalArea ρ (rect x y) ∨ MedialArea ρ (rect x y) := by
  -- let the rational line `ρ` be laid out, and the square on `x`, the rectangle, and the
  -- square on `y` be applied to it, making `f`, `k`, `l` as breadths [Prop. 1.44]
  obtain ⟨f, hf⟩ := Area.apply ρ (sq x)
  obtain ⟨k, hk⟩ := Area.apply ρ (rect x y)
  obtain ⟨l, hl⟩ := Area.apply ρ (sq y)
  -- the squares are medial: `f` and `l` are rational [Prop. 10.22]
  obtain ⟨hfr, -⟩ := proposition_22 hx (Rational.self ρ) hf
  obtain ⟨hlr, -⟩ := proposition_22 hy (Rational.self ρ) hl
  -- the squares are commensurable, and as the one applied area to the other, so `f` to
  -- `l` [Prop. 6.1]: `f` is commensurable in length with `l` [Prop. 10.11]
  have h₁ : Commensurable (rect ρ f) (rect ρ l) := by rw [hf, hl]; exact h.1
  have h₂ := (proposition_11 (rect_proportion' f l ρ) Area.divisible Length.divisible).1
    h₁
  -- so the rectangle contained by `f` and `l` is rational [Prop. 10.19]
  have h₃ := proposition_19 hfr hlr h₂
  -- as `x` is to `y`, so the square on `x` to the rectangle, and the rectangle to the
  -- square on `y` [Prop. 6.1]
  have h₄ := Elements.Book5.proposition_11 (proposition_21_lemma x y).1.symm
    (rect_proportion x y y).symm
  -- so as the area applied with breadth `f` is to that with `k`, so that with `k` to that
  -- with `l`; and so as `f` is to `k`, so `k` to `l` [Props. 6.1, 5.11]
  rw [← hf, ← hk, ← sq_eq_rect, ← hl] at h₄
  have h₅ : Proportion f k k l := Elements.Book5.proposition_11
    (rect_proportion' f k ρ).symm
    (Elements.Book5.proposition_11 h₄ (rect_proportion' k l ρ))
  -- so the rectangle contained by `f` and `l` is the square on `k` [Prop. 6.17]: it is
  -- rational, and so `k` [Def. 10.3]
  have hkr : Rational ρ k := Rational.of_sq (rect_eq_sq_of_proportion h₅ ▸ h₃)
  rw [← hk]
  by_cases hkρ : Commensurable ρ k
  · -- `k` commensurable in length with `ρ`: the rectangle is rational [Prop. 10.19]
    exact Or.inl (proposition_19 (Rational.self ρ) hkr hkρ)
  · -- else `ρ` and `k` are rational, commensurable in square only: it is medial [Prop.
    -- 10.21]
    exact Or.inr
      ⟨ρ, k, Rational.self ρ, hkr, ⟨(Rational.self ρ).inSquare_of hkr, hkρ⟩, rfl⟩

end Elements.Book10
