import Elements.Book10.Prop032

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/--
The figure of 10.33–10.35. To the greater `l` of two lines is applied the square on the
half `h` of the lesser `a`, falling short by a square [Prop. 6.28], cutting `l` into `x`
and `y`; on `l` the semicircle is drawn, the perpendicular at the cut meets it, and the
lines `u`, `v` are joined to the ends [Props. 3.31, 1.11]. Then the rectangle contained by
`l`, `x` is the square on `u`, by `l`, `y` the square on `v`, the squares on `u`, `v` are
the square on `l` [Prop. 1.47], and the perpendicular is `h`, for its square is the
rectangle contained by `x`, `y` [Prop. 10.32 lem.]: so the rectangle contained by `l`, `h`
is that contained by `u`, `v` [Prop. 10.32 lem.].
-/
theorem figure_33 {l a : Length} (hal : a < l) :
    ∃ h x y u v, h + h = a ∧ x + y = l ∧ rect x y = sq h ∧ rect l x = sq u ∧
      rect l y = sq v ∧ sq u + sq v = sq l ∧ rect l h = rect u v := by
  obtain ⟨h, x, y, hh, hxy, hr⟩ := exists_application hal
  obtain ⟨u, v, p, hu, hv, hl⟩ := Length.semicircle hxy
  obtain ⟨h₁, h₂, h₃, h₄⟩ := proposition_32_lemma hxy hu hv hl
  have hp : p = h := sq_inj (h₃.symm.trans hr)
  subst hp
  exact ⟨p, x, y, u, v, hh, hxy, hr, h₁, h₂, hl, h₄⟩

/-- Of two unequal lines with conditions that do not depend on their order, the greater
can be named first. -/
theorem exists_ordered {P : Length → Length → Prop} (hP : ∀ {x y}, P x y → P y x)
    {u v : Length} (h : P u v) (hne : u ≠ v) : ∃ x y, P x y ∧ y < x := by
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact ⟨v, u, hP h, hlt⟩
  · exact ⟨u, v, h, hlt⟩

/-- In the figure, if `x` and `y` are incommensurable in length, the squares on `u` and
`v` are incommensurable [Props. 6.1, 10.11]. -/
theorem figure_33_incomm {l x y u v : Length} (hu : rect l x = sq u)
    (hv : rect l y = sq v)
    (hxy : ¬ Commensurable x y) : ¬ CommensurableInSquare u v := by
  have h := rect_proportion' x y l
  rw [hu, hv] at h
  exact (proposition_11 h.symm Length.divisible Area.divisible).2 hxy

/-- In the figure, the rectangle contained by `l` and `a` is double that contained by `l`
and `h`, and commensurable with it [Props. 2.1, 10.6]. -/
theorem figure_33_double {l a h : Length} (hh : h + h = a) :
    Commensurable (rect l a) (rect l h) := by
  rw [← hh, rect_add]
  exact double_commensurable _

/-- To find two lines incommensurable in square, the sum of the squares on them rational,
the rectangle contained by them medial. -/
theorem proposition_33 : ∃ x y, MajorTerms ρ x y := by
  -- let rational `l`, `a`, commensurable in square only, be laid out, the square on `l`
  -- exceeding that on `a` by the square on a line incommensurable with `l` [Prop. 10.30]
  obtain ⟨l, a, ⟨hl, ha, hla, hal⟩, he⟩ := proposition_30 (ρ := ρ)
  obtain ⟨h, x, y, u, v, hh, hxy, hr, hu, hv, hsq, hrect⟩ := figure_33 hal
  -- `x` is incommensurable in length with `y` [Prop. 10.18], so the squares on `u`, `v`
  have hx := (proposition_18 hal hh hxy hr).mpr he
  have h₁ := figure_33_incomm hu hv hx
  -- the square on `l` is rational, and so the squares on `u`, `v` [Prop. 1.47]
  have h₂ : RationalArea ρ (sq u + sq v) := hsq ▸ hl.sq_rational
  -- the rectangle contained by `l`, `a` is medial [Prop. 10.21], so that contained by
  -- `l`, `h` [Prop. 10.23 corr.], which is that contained by `u`, `v` [Prop. 10.32 lem.]
  have h₃ : MedialArea ρ (rect u v) :=
    hrect ▸ proposition_23_corollary ⟨l, a, hl, ha, hla, rfl⟩ (figure_33_double hh).symm
  refine exists_ordered (P := fun x y => ¬ CommensurableInSquare x y ∧
    RationalArea ρ (sq x + sq y) ∧ MedialArea ρ (rect x y)) ?_ ⟨h₁, h₂, h₃⟩ ?_ |>.imp
    fun x ⟨y, h, hyx⟩ => ⟨y, h.1, h.2.1, h.2.2, hyx⟩
  · rintro x y ⟨h₁, h₂, h₃⟩
    exact ⟨fun h => h₁ h.symm, add_comm (sq x) _ ▸ h₂, rect_comm x y ▸ h₃⟩
  · rintro rfl
    exact h₁ (Commensurable.refl _)

end Elements.Book10
