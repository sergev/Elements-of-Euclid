import Elements.Book10.Prop112

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- The square on a rational line `a`, applied to an apotome `l` with terms `x > y`, makes
as breadth a binomial `f` whose terms `x'`, `y'` are commensurable with the terms of the
apotome, and in the same ratio; and the binomial is of the same order as the apotome. -/
theorem proposition_113 {a l x y f : Length} (ha : Rational ρ a) (h : BinomialTerms ρ x y)
    (hl : l + y = x) (hf : rect l f = sq a) :
    ∃ x' y', f = x' + y' ∧ BinomialTerms ρ x' y' ∧ Commensurable x x' ∧
      Commensurable y y' ∧ Proportion x y x' y' ∧
      ∀ r k, OrderTerms ρ r k x y → OrderTerms ρ r k x' y' := by
  obtain ⟨hx, hy, hxy, hyx⟩ := h
  -- let the rectangle contained by `x` and `g` be the square on `a`: `g` is rational and
  -- commensurable with `x` [Prop. 10.20]; as `x` is to `l`, so `f` to `g` [Prop. 6.16],
  -- and `f` is the greater [Props. 5.16, 5.14]; `f` is `g` and `e`
  obtain ⟨g, hg⟩ := Area.apply x (sq a)
  obtain ⟨hgr, hgx⟩ := proposition_20 hx ha.sq_rational hg
  have h₁ : Proportion x l f g := proportion_of_rect_eq (hg.trans hf.symm)
  have hgf : g < f := lt_of_proportion h₁ (hl ▸ Magnitude.lt_add l y)
  obtain ⟨e, he⟩ := Magnitude.remainder g f hgf
  -- via conversion, as `x` is to `y`, so `f` to `e` [Prop. 5.19 corr.]
  have h₂ : Proportion x y f e := by
    rw [← hl, ← he, add_comm l y, add_comm g e] at h₁ ⊢
    exact Elements.Book5.proposition_19_corollary h₁
  -- let `e` be cut into `s`, `t`, as `f` is to `e` [Prop. 6.10]: the remainder `g + t` is
  -- to `s` as `f` to `e` [Prop. 5.19], so as `x` to `y` [Prop. 5.11]
  obtain ⟨s, t, hst, h₃⟩ := Length.cut e f e
  have h₄ : Proportion (g + t) s f e := by
    have h₅ := h₃
    rw [← he, ← hst] at h₅ ⊢
    rw [show g + (s + t) = s + (g + t) by ac_rfl, add_comm s t] at h₅ ⊢
    exact Elements.Book5.proposition_19 h₅
  have h₆ := Elements.Book5.proposition_11 h₂ h₄.symm
  -- they are commensurable in square only [Prop. 10.11]; and `g + t` is to `s` as `s` to
  -- `t` [Prop. 5.11]: as `g + t` to `t`, so the square on `g + t` to that on `s` [Def.
  -- 5.9], so `g + t` is commensurable with `t` [Prop. 10.11], and with `g` [Prop. 10.15]
  have hgs := hxy.of_proportion h₆
  have h₇ : Proportion (g + t) s s t := Elements.Book5.proposition_11 h₄ h₃
  obtain ⟨c, hc₁, hc₂⟩ := squaredRatio_sq (g + t) s
  have hct : c = t := Elements.Book5.proposition_9'
    (Elements.Book5.proposition_11 hc₁.symm h₇)
  subst hct
  have h₈ := (proposition_11 hc₂ Area.divisible Length.divisible).1 hgs.1
  have h₉ : Commensurable (g + c) g := by
    rw [add_comm g c] at h₈ ⊢; exact (proposition_15.1 (proposition_15.2 h₈)).2
  -- so `g + t` is rational, commensurable with `x` [Prop. 10.12]; alternately, `s` with
  -- `y` [Props. 5.16, 10.11]
  have hxg : Commensurable x (g + c) := proposition_12 Length.divisible hgx.symm h₉
  have hys := (proposition_11 (Elements.Book5.proposition_16 h₆) Length.divisible
    Length.divisible).1 hxg
  have hcr : Rational ρ (g + c) := hx.of_comm hxg.symm
  refine ⟨g + c, s, ?_, ⟨hcr, hcr.of_inSquare hgs.1.symm, hgs, lt_of_proportion h₆ hyx⟩,
    hxg, hys, h₆, fun r k hk => OrderTerms.transfers hk h₆ hxg hys⟩
  rw [← he, ← hst]; ac_rfl

end Elements.Book10
