import Elements.Book10.Prop058

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- If an area is contained by a rational line `r` and a sixth binomial, the square root
`z` of the area is the square root of two medial areas. -/
theorem proposition_59 {r l z : Length} (hr : Rational ρ r) (hl : SixthBinomial ρ r l)
    (hz : sq z = rect r l) : SideTwoMedials ρ z := by
  -- the sixth binomial divided into its terms `x > y`, neither commensurable with `r`
  -- [Def. 10.II.6], and the construction of 10.54
  obtain ⟨x, y, ⟨⟨hx, hy, hxy, hyx⟩, hexc, hxr, hyr⟩, rfl⟩ := hl
  obtain ⟨x₁, x₂, f, m, n, hf, hx₁₂, hr₁₂, -, hm, hn, hmn, hnm, hsum, htwice⟩ :=
    proposition_54_construction r hyx
  -- `x₁`, `x₂` are incommensurable [Prop. 10.18], so `m`, `n` in square
  have h₁ := (proposition_18 hyx hf hx₁₂ hr₁₂).mpr hexc
  -- the squares on `m`, `n`, the rectangle contained by `r`, `x`, are medial; and the
  -- rectangle contained by `m`, `n`, that contained by `r`, `f`, is medial [Prop. 10.21]
  have hs : MedialArea ρ (sq m + sq n) := hsum ▸ medial_rect hr hx hxr
  have hfy : Commensurable f y := hf ▸ (double_commensurable f).symm
  have hrect : MedialArea ρ (rect m n) := hmn ▸ medial_rect hr (hy.of_comm hfy)
    (proposition_13 Length.divisible hfy.symm hyr)
  -- `x` is incommensurable with `y`, so with `f` [Prop. 10.13]: the rectangles on `r`
  -- are incommensurable [Props. 6.1, 10.11]
  have hxf : ¬ Commensurable x f := fun h' => hxy.2
    (proposition_12 Length.divisible h' hfy.symm)
  have hi : ¬ Commensurable (sq m + sq n) (rect m n) := by
    rw [hsum, hmn, rect_commensurable_iff]; exact hxf
  exact ⟨m, n, ⟨construction_incomm_sq h₁ hm hn, hs, hrect, hi, hnm⟩,
    side_eq_add hsum htwice hz⟩

/-- 10.59, lemma: if a line is cut unequally, the squares on the pieces exceed twice the
rectangle contained by them. -/
theorem proposition_59_lemma {x y : Length} (h : y < x) :
    (2 : ℕ+) • rect x y < sq x + sq y := by
  -- let the line be cut in half, `e` the half, `t` between the cuts
  obtain ⟨e, he⟩ := Length.part (x + y) 2
  rw [show (2 : ℕ+) = 1 + 1 from rfl, Magnitude.mult_succ, Magnitude.one_mult] at he
  have hex : e < x := lt_of_not_ge fun h' =>
    absurd he (ne_of_lt (add_lt_add_of_le_of_lt h' (lt_of_lt_of_le h h')))
  obtain ⟨t, ht⟩ := Magnitude.remainder e x hex
  have hyt : y + t = e := add_right_cancel (b := e) (by
    rw [add_assoc, add_comm t e, ht, add_comm y x, he])
  -- the rectangle, with the square on `t`, is the square on the half [Prop. 2.5]: so
  -- twice the rectangle is less than double the square on the half; and the squares are
  -- double the squares on the half and on `t` [Prop. 2.9]
  have h₁ : rect x y < sq e := (rect_add_sq ht hyt) ▸ Magnitude.lt_add _ _
  rw [sq_add_sq_half ht hyt]
  exact Magnitude.mult_lt_mult 2 (lt_trans h₁ (Magnitude.lt_add _ _))

end Elements.Book10
