import Elements.Book10.Prop111

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- Terms of an order carry over to terms commensurable with them, in the same ratio. -/
theorem OrderTerms.transfers {r : Length} {k : Fin 6} : Transfers (OrderTerms ρ r k) :=
  match k with
  | ⟨0, _⟩ => firstTerms_transfers
  | ⟨1, _⟩ => secondTerms_transfers
  | ⟨2, _⟩ => thirdTerms_transfers
  | ⟨3, _⟩ => fourthTerms_transfers
  | ⟨4, _⟩ => fifthTerms_transfers
  | ⟨5, _⟩ => sixthTerms_transfers

/--
The square on a rational line `a`, applied to a binomial with terms `x > y`, makes as
breadth an apotome `f` whose terms `x'`, `y'` are commensurable with the terms of the
binomial, and in the same ratio; and the apotome is of the same order as the binomial.
Heiberg regards 10.112–10.115 as early interpolations.
-/
theorem proposition_112 {a x y f : Length} (ha : Rational ρ a) (h : BinomialTerms ρ x y)
    (hf : rect (x + y) f = sq a) :
    ∃ x' y', f + y' = x' ∧ BinomialTerms ρ x' y' ∧ Commensurable x x' ∧
      Commensurable y y' ∧ Proportion x y x' y' ∧
      ∀ r k, OrderTerms ρ r k x y → OrderTerms ρ r k x' y' := by
  obtain ⟨hx, hy, hxy, hyx⟩ := h
  -- let the rectangle contained by `y` and `g` be the square on `a` [Prop. 1.44]: as
  -- `x + y` is to `y`, so `g` to `f` [Prop. 6.16], and `g` is the greater [Props. 5.16,
  -- 5.14]; `g` is `f` and `h`
  obtain ⟨g, hg⟩ := Area.apply y (sq a)
  have h₁ : Proportion (x + y) y g f := proportion_of_rect_eq (hf.trans hg.symm)
  have hfg : f < g := lt_of_proportion h₁ (Magnitude.lt_add' x y)
  obtain ⟨h, hh⟩ := Magnitude.remainder f g hfg
  -- via separation, as `x` is to `y`, so `h` to `f` [Prop. 5.17]
  rw [← hh, add_comm f h] at h₁
  have h₂ := Elements.Book5.proposition_17 h₁
  -- let it be contrived that as `h` is to `f`, so `f + q` to `q` [Prop. 6.12]: so as `x`
  -- to `y`, so `p = f + q` to `q` [Prop. 5.11]
  obtain ⟨q, hq⟩ := Length.extend (lt_of_proportion h₂ hyx)
  have h₃ := Elements.Book5.proposition_11 h₂ hq
  -- the whole `h + p` is to `p` as `p` to `q` [Props. 5.12, 5.11]
  have h₄ : Proportion (h + (f + q)) (f + q) (f + q) q :=
    Elements.Book5.proposition_11 (proportion_add hq).symm hq
  -- the squares on `x`, `y` are commensurable, so those on `h + p`, `p` [Props. 6.22,
  -- 10.11]; and as the square on `h + p` is to that on `p`, so `h + p` to `q` [Def. 5.9]:
  -- `h + p` is commensurable with `q` [Prop. 10.11], and so `g = h + f` with `q` [Prop.
  -- 10.15]
  have h₅ := (proposition_11 (proportion_sq.mp (Elements.Book5.proposition_11 h₃ h₄.symm))
    Area.divisible Area.divisible).1 hxy.1
  obtain ⟨e, he₁, he₂⟩ := squaredRatio_sq (h + (f + q)) (f + q)
  have hqe : e = q := Elements.Book5.proposition_9'
    (Elements.Book5.proposition_11 he₁.symm h₄)
  subst hqe
  have h₆ := (proposition_11 he₂ Area.divisible Length.divisible).1 h₅
  rw [← add_assoc, add_comm (h + f) e] at h₆
  have hqg : Commensurable e (h + f) := proposition_15.2 h₆
  -- the rectangle contained by `y`, `g` is rational, so `g` is rational, commensurable
  -- with `y` [Prop. 10.20]; and so `q` [Def. 10.3, Prop. 10.12]
  rw [add_comm h f, hh] at hqg
  obtain ⟨hgr, hgy⟩ := proposition_20 hy ha.sq_rational hg
  have hqy : Commensurable e y := proposition_12 Length.divisible hqg hgy.symm
  have hqr : Rational ρ e := hy.of_comm hqy
  -- as `x` is to `y`, so `p` to `q`: they are commensurable in square only [Prop. 10.11],
  -- `p` is rational; and `x` is commensurable with `p` [Props. 5.16, 10.11]
  have hpq := hxy.of_proportion h₃
  have hxp := (proposition_11 (Elements.Book5.proposition_16 h₃).symm Length.divisible
    Length.divisible).1 hqy.symm
  -- `f` is the apotome of `p`, `q`, of the same order as the binomial [Props. 10.14,
  -- 10.12, 10.13]
  refine ⟨f + e, e, rfl, ⟨hqr.of_inSquare hpq.1, hqr, hpq, Magnitude.lt_add' f e⟩,
    hxp, hqy.symm, h₃, fun r k hk => OrderTerms.transfers hk h₃ hxp hqy.symm⟩

end Elements.Book10
