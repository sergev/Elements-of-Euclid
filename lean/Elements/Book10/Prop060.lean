import Elements.Book10.Prop059

namespace Elements.Book10

open Elements.Book5 Elements.Book5.Magnitude

variable {ρ : Length}

/--
The construction of 10.60–10.65 (and 10.97–10.102). The squares on the terms `x > y` and
the rectangle contained by them, applied to `r`, make `k₁`, `k₂`, `h` as breadths [Prop.
1.44]; twice the rectangle makes `h + h`. The rectangle applied with breadth `h` is the
mean proportional of the squares [Prop. 10.53 lem.], so `h` of `k₁`, `k₂` [Prop. 6.1], and
the rectangle contained by `k₁`, `k₂` is the square on `h` [Prop. 6.17]. The squares
exceed twice the rectangle [Prop. 10.59 lem.], so `k₁ + k₂` exceeds `h + h` [Prop. 6.1].
-/
theorem proposition_60_construction (r : Length) {x y : Length} (hyx : y < x) :
    ∃ k₁ k₂ h, rect r k₁ = sq x ∧ rect r k₂ = sq y ∧ rect r h = rect x y ∧
      rect k₁ k₂ = sq h ∧ h + h < k₁ + k₂ ∧ rect r (k₁ + k₂) = sq x + sq y ∧
      rect r (h + h) = (2 : ℕ+) • rect x y := by
  obtain ⟨k₁, h₁⟩ := Area.apply r (sq x)
  obtain ⟨k₂, h₂⟩ := Area.apply r (sq y)
  obtain ⟨h, h₃⟩ := Area.apply r (rect x y)
  have h₄ : rect r (h + h) = (2 : ℕ+) • rect x y := by
    rw [rect_add, h₃, show (2 : ℕ+) = 1 + 1 from rfl, mult_succ, one_mult]
  have h₅ := (proposition_53_lemma x y).1
  rw [← h₁, ← h₂, ← h₃] at h₅
  have h₆ : Proportion k₁ h h k₂ := Elements.Book5.proposition_11
    (rect_proportion' k₁ h r).symm (Elements.Book5.proposition_11 h₅
      (rect_proportion' h k₂ r))
  have h₇ : rect r (k₁ + k₂) = sq x + sq y := by rw [rect_add, h₁, h₂]
  refine ⟨k₁, k₂, h, h₁, h₂, h₃, rect_eq_sq_of_proportion h₆, ?_, h₇, h₄⟩
  exact rect_lt_rect.mp (by rw [h₄, h₇]; exact proposition_59_lemma hyx)

/-- In the construction, the square on `x + y` applied to `r` makes as breadth the sum of
the breadths of the squares and of twice the rectangle [Prop. 2.4]. -/
theorem breadth_eq_add {r x y g e d : Length} (hg : rect r g = sq (x + y))
    (h₁ : rect r e = sq x + sq y) (h₂ : rect r d = (2 : ℕ+) • rect x y) : g = e + d :=
  rect_inj (by rw [hg, rect_add, h₁, h₂, sq_add])

/-- The terms of 10.60: the squares on the terms `x > y` of a binomial and twice the
rectangle, applied to a rational line `r`, make as breadths the terms of a first
binomial. Shared with 10.97. -/
theorem proposition_60_terms {r x y : Length} (hr : Rational ρ r)
    (h : BinomialTerms ρ x y) :
    ∃ e d, FirstTerms ρ r e d ∧ rect r e = sq x + sq y ∧
      rect r d = (2 : ℕ+) • rect x y := by
  obtain ⟨hx, hy, hxy, hyx⟩ := h
  obtain ⟨k₁, k₂, h, h₁, h₂, -, hk, hlt, hs, h2⟩ := proposition_60_construction r hyx
  -- the squares on `x`, `y` are rational [Prop. 10.15]: `k₁ + k₂` is rational,
  -- commensurable in length with `r` [Prop. 10.20]
  obtain ⟨her, heρ⟩ := proposition_20 hr
    (hx.sq_rational.of_comm (proposition_15.1 hxy.1).1) hs
  -- twice the rectangle is medial [Prop. 10.21]: `h + h` is rational, incommensurable in
  -- length with `r` [Prop. 10.22]
  obtain ⟨hdr, hdρ⟩ := proposition_22' (MedialArea.twice ⟨x, y, hx, hy, hxy, rfl⟩) hr h2
  -- so `k₁ + k₂`, `h + h` are incommensurable in length [Prop. 10.13]
  have hed : ¬ Commensurable (k₁ + k₂) (h + h) :=
    fun h' => hdρ (proposition_12 Length.divisible h'.symm heρ.symm)
  -- `k₁`, `k₂` are commensurable, the squares being so [Props. 6.1, 10.11]: so the square
  -- on `k₁ + k₂` exceeds that on `h + h` by the square on a line commensurable with it
  -- [Prop. 10.17]
  have hk₁₂ : Commensurable k₁ k₂ := (rect_commensurable_iff r).mp
    (by rw [h₁, h₂]; exact hxy.1)
  have hexc := (proposition_17 hlt rfl rfl hk).mp hk₁₂
  exact ⟨k₁ + k₂, h + h, ⟨⟨her, hdr, ⟨her.inSquare_of hdr, hed⟩, hlt⟩, hexc, heρ⟩, hs, h2⟩

/-- The square on a binomial, applied to a rational line `r`, makes as breadth a first
binomial. -/
theorem proposition_60 {r l g : Length} (hl : Binomial ρ l) (hr : Rational ρ r)
    (hg : rect r g = sq l) : FirstBinomial ρ r g := by
  obtain ⟨x, y, h, rfl⟩ := hl
  obtain ⟨e, d, hed, he, hd⟩ := proposition_60_terms hr h
  -- the breadth is `e + d` [Prop. 2.4]
  exact ⟨e, d, hed, breadth_eq_add hg he hd⟩

end Elements.Book10
