import Elements.Book10.Prop022

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- A line commensurable with a medial line is medial. "Commensurable" is in length or in
square only; both give the squares commensurable, which is all the proof uses. -/
theorem proposition_23 {a b : Length} (ha : Medial ρ a) (h : CommensurableInSquare b a) :
    Medial ρ b := by
  -- let the rational line `ρ` be set out, and the square on `a` applied to it, making `e`
  -- as breadth [Prop. 1.44]: `e` is rational, and incommensurable in length with `ρ`
  -- [Prop. 10.22]
  obtain ⟨e, he⟩ := Area.apply ρ (sq a)
  obtain ⟨her, heρ⟩ := proposition_22 ha (Rational.self ρ) he
  -- and let the square on `b` be applied to it, making `f`
  obtain ⟨f, hf⟩ := Area.apply ρ (sq b)
  -- the squares are commensurable, and as the one rectangle is to the other, so `e` to
  -- `f` [Prop. 6.1]: `e` is commensurable in length with `f` [Prop. 10.11]
  have h₁ : Commensurable (rect ρ e) (rect ρ f) := by rw [he, hf]; exact h.symm
  have h₂ := (proposition_11 (rect_proportion' e f ρ) Area.divisible Length.divisible).1
    h₁
  -- so `f` is rational [Def. 10.3], and incommensurable in length with `ρ` [Prop. 10.13]
  have hfr : Rational ρ f := her.of_comm h₂.symm
  have hfρ : ¬ Commensurable f ρ := proposition_13 Length.divisible h₂ heρ
  -- `ρ` and `f` are rational, commensurable in square only: the square root of the
  -- rectangle contained by them is medial [Prop. 10.21], and it is `b`
  exact ⟨ρ, f, Rational.self ρ, hfr,
    ⟨(Rational.self ρ).inSquare_of hfr, fun h => hfρ h.symm⟩, hf.symm⟩

/-- 10.23, corollary: an area commensurable with a medial area is medial. -/
theorem proposition_23_corollary {A B : Area} (hA : MedialArea ρ A)
    (h : Commensurable B A) : MedialArea ρ B := by
  -- their sides [Prop. 2.14]: the side of `A` is medial, and so the side of `B`
  obtain ⟨a, rfl⟩ := Area.side A
  obtain ⟨b, rfl⟩ := Area.side B
  exact proposition_23 hA h

end Elements.Book10
