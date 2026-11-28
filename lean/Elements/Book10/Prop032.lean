import Elements.Book10.Prop031

namespace Elements.Book10

open Elements.Book5 Elements.Book7 Number

variable {ρ : Length}

/-- For rational `a`, `c`, a rational line commensurable in square only with both. Euclid
lays it down without saying how. Of the lines whose squares are to the square on `a` as
`2` and as `3` to `4` [Prop. 10.6 corr.], both commensurable in square only with `a`, one
is incommensurable in length with `c`, for they are so with one another: their squares are
as `6` to `9` [Props. 10.9, 10.12]. -/
theorem exists_inSquareOnly_both {a c : Length} (ha : Rational ρ a) (hc : Rational ρ c) :
    ∃ b, Rational ρ b ∧ InSquareOnly a b ∧ InSquareOnly b c := by
  have sq4 : SquareNumber ((4 : ℕ+) : ℕ) := ⟨2, by decide, rfl⟩
  have sq9 : SquareNumber ((9 : ℕ+) : ℕ) := ⟨3, by decide, rfl⟩
  obtain ⟨-, b₂, -, h₂⟩ := proposition_6_corollary 4 2 a
  obtain ⟨-, b₃, -, h₃⟩ := proposition_6_corollary 4 3 a
  have hab₂ := inSquareOnly_of_ratio h₂ (not_square_ratio_of (Or.inl ⟨sq4, by decide,
    not_square_of_between (k := 1) (by decide) (by decide)⟩))
  have hab₃ := inSquareOnly_of_ratio h₃ (not_square_ratio_of (Or.inl ⟨sq4, by decide,
    not_square_of_between (k := 1) (by decide) (by decide)⟩))
  have hb₂ : Rational ρ b₂ := ha.of_inSquare hab₂.1.symm
  have hb₃ : Rational ρ b₃ := ha.of_inSquare hab₃.1.symm
  -- the squares on `b₂` and `b₃` are as `2` to `3` [Prop. 5.22], that is, as `6` to `9`
  have h₄ : Proportion ((6 : ℕ+) : Number) ((9 : ℕ+) : Number) (sq b₂) (sq b₃) :=
    Elements.Book5.proposition_11 (number_proportion (by decide))
      (Elements.Book5.proposition_22' (Elements.Book5.proposition_7_corollary h₂) h₃)
  have hb₂₃ := inSquareOnly_of_ratio h₄ (not_square_ratio_of (Or.inr ⟨sq9, by decide,
    not_square_of_between (k := 2) (by decide) (by decide)⟩))
  by_cases h : Commensurable b₂ c
  · exact ⟨b₃, hb₃, hab₃, hb₃.inSquare_of hc,
      fun h' => hb₂₃.2 (proposition_12 Length.divisible h h')⟩
  · exact ⟨b₂, hb₂, hab₂, hb₂.inSquare_of hc, h⟩

/-- The construction of 10.32: from rational `a`, `c` commensurable in square only, and
`b` commensurable in square only with both, the square on `d` equal to the rectangle
contained by `a`, `b` [Prop. 2.14], and the rectangle contained by `d`, `e` equal to that
contained by `b`, `c` [Prop. 1.44]: `d`, `e` are medial, commensurable in square only,
contain a medial area, and `a ∶ c ∷ d ∶ e`. -/
theorem proposition_32_construction {a c : Length} (h : BinomialTerms ρ a c) :
    ∃ d e, SecondBimedialTerms ρ d e ∧ Proportion a c d e := by
  obtain ⟨ha, hc, hac, hca⟩ := h
  obtain ⟨b, hb, hab, hbc⟩ := exists_inSquareOnly_both ha hc
  obtain ⟨d, hd⟩ := Area.side (rect a b)
  -- the square on `d` is medial, and `d` is medial [Prop. 10.21]
  have hdm : Medial ρ d := ⟨a, b, ha, hb, hab, hd⟩
  obtain ⟨e, he⟩ := Area.apply d (rect b c)
  -- as the rectangle contained by `a`, `b` is to that contained by `b`, `c`, so `a` to
  -- `c` [Prop. 10.21 lem.]; that is, the square on `d` to the rectangle contained by `d`,
  -- `e`, that is, `d` to `e` [Prop. 10.21 lem.]
  have h₁ : Proportion a c d e := by
    have h₂ := rect_proportion a c b
    rw [rect_comm c b, ← hd, ← he] at h₂
    exact Elements.Book5.proposition_11 h₂.symm (proposition_21_lemma d e).1.symm
  -- `d`, `e` are commensurable in square only [Prop. 10.11], and `e` is medial [Prop.
  -- 10.23]; the rectangle contained by them, that contained by `b`, `c`, is medial [Prop.
  -- 10.21]
  have hde := hac.of_proportion h₁
  exact ⟨d, e, ⟨hdm, proposition_23 hdm hde.1.symm, hde, ⟨b, c, hb, hc, hbc, he⟩,
    lt_of_proportion h₁ hca⟩, h₁⟩

/-- To find two medial lines commensurable in square only, containing a medial area, the
square on the greater exceeding that on the lesser by the square on a line commensurable
in length with the greater. -/
theorem proposition_32 : ∃ x y, SecondBimedialTerms ρ x y ∧ ExceedsComm x y := by
  -- let rational `a`, `c` be laid out, as in 10.29 [Prop. 10.29]
  obtain ⟨a, c, hac, he⟩ := proposition_29 (ρ := ρ)
  obtain ⟨d, e, hde, h⟩ := proposition_32_construction hac
  -- the square on `d` exceeds that on `e` by the square on a line commensurable with `d`
  -- [Prop. 10.14]
  exact ⟨d, e, hde, (proposition_14' h).1 he⟩

/-- 10.32, Euclid's closing remark: the same with a line incommensurable in length, from
10.30. -/
theorem proposition_32' : ∃ x y, SecondBimedialTerms ρ x y ∧ ExceedsIncomm x y := by
  obtain ⟨a, c, hac, he⟩ := proposition_30 (ρ := ρ)
  obtain ⟨d, e, hde, h⟩ := proposition_32_construction hac
  exact ⟨d, e, hde, (proposition_14' h).2 he⟩

/--
10.32, lemma: in a right-angled triangle with legs `u`, `v` and base `l`, the
perpendicular `p` from the right angle cutting the base into `m` (by `u`) and `n`: the
rectangle contained by `l`, `m` is the square on `u`; by `l`, `n` the square on `v`; by
`m`, `n` the square on `p`; and by `l`, `p` the rectangle contained by `u`, `v`. The right
angles are given by the squares [Prop. 1.47].
-/
theorem proposition_32_lemma {l u v m n p : Length} (hmn : m + n = l)
    (hu : sq p + sq m = sq u) (hv : sq p + sq n = sq v) (hl : sq u + sq v = sq l) :
    rect l m = sq u ∧ rect l n = sq v ∧ rect m n = sq p ∧ rect l p = rect u v := by
  -- the triangles are similar to the whole and to one another [Prop. 6.8]: as `l` is to
  -- `u`, so `u` to `m` [Prop. 6.4], and similarly for `v`; the perpendicular is the mean
  -- proportional of `m`, `n` [Prop. 6.8 corr.]; and as `l` is to `v`, so `u` to `p`
  -- [Prop. 6.4]
  obtain ⟨h₁, h₂, h₃, h₄⟩ := right_triangle_proportions hmn hu hv hl
  -- [Props. 6.17, 6.16]
  exact ⟨rect_eq_sq_of_proportion h₁, rect_eq_sq_of_proportion h₂,
    rect_eq_sq_of_proportion h₃, (rect_eq_of_proportion h₄).trans (rect_comm v u)⟩

end Elements.Book10
