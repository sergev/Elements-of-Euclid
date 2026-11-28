import Elements.Book10.Prop053

namespace Elements.Book10

open Elements.Book5 Elements.Book5.Magnitude

variable {ρ : Length}

/-- Rectangles on the same line are commensurable exactly when their other sides are
[Props. 6.1, 10.11]. -/
theorem rect_commensurable_iff (r : Length) {a b : Length} :
    Commensurable (rect r a) (rect r b) ↔ Commensurable a b :=
  ⟨(proposition_11 (rect_proportion' a b r) Area.divisible Length.divisible).1,
    (proposition_11 (rect_proportion' a b r).symm Length.divisible Area.divisible).1⟩

/-- The rectangle contained by rational lines commensurable in square only is medial
[Prop. 10.21]. -/
theorem medial_rect {r x : Length} (hr : Rational ρ r) (hx : Rational ρ x)
    (h : ¬ Commensurable x r) : MedialArea ρ (rect r x) :=
  ⟨r, x, hr, hx, ⟨hr.inSquare_of hx, fun h' => h h'.symm⟩, rfl⟩

/--
The construction of 10.54–10.59 (and 10.91–10.96). The terms `x > y` of a line applied to
`r`: to `x` is applied the fourth part of the square on `y`, the square on its half `f`,
falling short by a square [Prop. 6.28], cutting it into `x₁ > x₂`; the squares on `m` and
`n` are made equal to the rectangles contained by `r` and `x₁`, `x₂` [Prop. 2.14]. The
rectangle contained by `r`, `f` is the mean proportional of these [Props. 6.17, 6.1], as
the rectangle contained by `m`, `n` is of the squares [Prop. 10.53 lem.], so they are
equal; and the squares on `m`, `n` are the rectangle contained by `r` and `x`, twice the
rectangle contained by them that contained by `r` and `y` [Prop. 2.1].
-/
theorem proposition_54_construction (r : Length) {x y : Length} (hyx : y < x) :
    ∃ x₁ x₂ f m n, f + f = y ∧ x₁ + x₂ = x ∧ rect x₁ x₂ = sq f ∧ x₂ < x₁ ∧
      sq m = rect r x₁ ∧ sq n = rect r x₂ ∧ rect m n = rect r f ∧ n < m ∧
      sq m + sq n = rect r x ∧ (2 : ℕ+) • rect m n = rect r y := by
  obtain ⟨f, x₁, x₂, hf, hx, hr⟩ := exists_application hyx
  -- the greater piece first; they are unequal, else `y` would be `x`
  wlog h₂₁ : x₂ < x₁ generalizing x₁ x₂
  · rcases (not_lt.mp h₂₁).lt_or_eq with hlt | rfl
    · exact this x₂ x₁ (add_comm x₂ x₁ ▸ hx) (rect_comm x₂ x₁ ▸ hr) hlt
    · exfalso
      have : f = x₁ := sq_inj (hr.symm.trans (sq_eq_rect x₁).symm)
      exact absurd (hf.symm.trans (this ▸ hx)) (ne_of_lt hyx)
  obtain ⟨m, hm⟩ := Area.side (rect r x₁)
  obtain ⟨n, hn⟩ := Area.side (rect r x₂)
  -- as `x₁` is to `f`, so `f` to `x₂` [Prop. 6.17]; so the rectangles on `r` [Prop. 6.1]
  have h₁ : Proportion x₁ f f x₂ := proportion_of_rect_eq (hr.trans (sq_eq_rect f))
  have h₂ : Proportion (rect r x₁) (rect r f) (rect r f) (rect r x₂) :=
    Elements.Book5.proposition_11 (rect_proportion' x₁ f r)
      (Elements.Book5.proposition_11 h₁ (rect_proportion' f x₂ r).symm)
  -- the rectangle contained by `m`, `n` is the mean proportional of the squares [Prop.
  -- 10.53 lem.]: so it is the rectangle contained by `r`, `f`
  have h₃ := (proposition_53_lemma m n).1
  rw [hm, hn] at h₃
  have hmn : rect m n = rect r f := mean_proportional_unique h₃ h₂
  have hnm : n < m := sq_lt_sq.mp (by rw [hm, hn]; exact rect_lt_rect.mpr h₂₁)
  refine ⟨x₁, x₂, f, m, n, hf, hx, hr, h₂₁, hm, hn, hmn, hnm, ?_, ?_⟩
  · rw [hm, hn, ← rect_add, hx]
  · rw [hmn, ← hf, rect_add, show (2 : ℕ+) = 1 + 1 from rfl, mult_succ, one_mult]

/-- The square on `m + n` is the rectangle contained by `r` and `x + y` [Prop. 2.4]:
`m + n` is the square root of the area [Prop. 10.53 lem.]. -/
theorem side_eq_add {r x y m n z : Length} (h₁ : sq m + sq n = rect r x)
    (h₂ : (2 : ℕ+) • rect m n = rect r y) (hz : sq z = rect r (x + y)) : z = m + n :=
  sq_inj (by rw [hz, sq_add, rect_add, ← h₁, ← h₂])

/-- In the construction, if `x`, `y` are incommensurable in length, so are `m`, `n`: `x₁`,
commensurable with `x`, is incommensurable with `f`, commensurable with `y` [Prop. 10.13];
so the rectangles on `r` [Props. 6.1, 10.11], that is, the square on `m` with the
rectangle contained by `m`, `n`, and so `m` with `n` [Props. 10.21 lem., 10.11]. -/
theorem construction_incomm {r x y x₁ f m n : Length} (hxy : ¬ Commensurable x y)
    (h₁x : Commensurable x₁ x) (hf : f + f = y) (hm : sq m = rect r x₁)
    (hmn : rect m n = rect r f) : ¬ Commensurable m n := by
  have hfy : Commensurable f y := hf ▸ (double_commensurable f).symm
  have h₃ : ¬ Commensurable x₁ f := fun h' => hxy (proposition_12 Length.divisible
    (proposition_12 Length.divisible h₁x.symm h'.symm) hfy.symm)
  have h₄ : ¬ Commensurable (sq m) (rect m n) := by
    rw [hm, hmn, rect_commensurable_iff]; exact h₃
  exact fun h' => h₄
    ((proposition_11 (proposition_21_lemma m n).1 Length.divisible Area.divisible).1 h')

/-- If an area is contained by a rational line `r` and a first binomial, the square root
`z` of the area is a binomial. -/
theorem proposition_54 {r l z : Length} (hr : Rational ρ r) (hl : FirstBinomial ρ r l)
    (hz : sq z = rect r l) : Binomial ρ z := by
  -- let the first binomial be divided into its terms `x > y` [Def. 10.II.1]
  obtain ⟨x, y, ⟨⟨hx, hy, hxy, hyx⟩, hexc, hxr⟩, rfl⟩ := hl
  obtain ⟨x₁, x₂, f, m, n, hf, hx₁₂, hr₁₂, h₂₁, hm, hn, hmn, hnm, hsum, htwice⟩ :=
    proposition_54_construction r hyx
  -- the square on `x` exceeds that on `y` by the square on a line commensurable with `x`:
  -- so `x₁`, `x₂` are commensurable [Prop. 10.17], and commensurable with `x` [Prop.
  -- 10.15], and with `r` [Prop. 10.12]: they are rational
  have h₁ := (proposition_17 hyx hf hx₁₂ hr₁₂).mpr hexc
  have h₁x : Commensurable x₁ x := hx₁₂ ▸ (proposition_15.1 h₁).1.symm
  have h₂x : Commensurable x₂ x := hx₁₂ ▸ (proposition_15.1 h₁).2.symm
  have h₁r := proposition_12 Length.divisible h₁x hxr.symm
  have h₂r := proposition_12 Length.divisible h₂x hxr.symm
  -- so the rectangles contained by `r` and them are rational [Prop. 10.19], and so the
  -- squares on `m`, `n`, and `m`, `n` are rational
  have hmr : Rational ρ m := Rational.of_sq
    (hm ▸ proposition_19 hr (hr.of_comm h₁r) h₁r.symm)
  have hnr : Rational ρ n := Rational.of_sq
    (hn ▸ proposition_19 hr (hr.of_comm h₂r) h₂r.symm)
  -- `x` is incommensurable in length with `y`: so `m` with `n`
  have h₅ := construction_incomm hxy.2 h₁x hf hm hmn
  -- `m`, `n` are rational, commensurable in square only: `m + n`, the square root of the
  -- area [Props. 10.53 lem., 2.4], is a binomial
  exact ⟨m, n, ⟨hmr, hnr, ⟨hmr.inSquare_of hnr, h₅⟩, hnm⟩, side_eq_add hsum htwice hz⟩

end Elements.Book10
