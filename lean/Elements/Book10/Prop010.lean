import Elements.Book10.Prop011

namespace Elements.Book10

open Elements.Book5 Number

/-- `4` is not to `3` as a square number to a square number: `4` is square, so `3` would
be square [Prop. 8.24], and it is not. -/
theorem not_square_ratio :
    ¬ ∃ c d : ℕ+, Proportion ((4 : ℕ+) : Number) ((3 : ℕ+) : Number)
      ((c : Number) * c) ((d : Number) * d) := by
  rintro ⟨c, d, h⟩
  have h' := number_proportion_iff.mp h
  simp only [val_coe, val_mul] at h'
  have h3 := Elements.Book8.proposition_24 c.pos d.pos (by decide) h' ⟨2, by decide, rfl⟩
  obtain ⟨p, hp, hp3⟩ := h3
  have : 2 * 2 ≤ p * p := Nat.mul_le_mul hp hp
  have h3 : ((3 : ℕ+) : ℕ) = 3 := rfl
  omega

/--
To find two lines incommensurable with a given line `a`, the one, `d`, in length only, the
other, `e`, in square too (and so also in length). Heiberg regards the whole proposition
as interpolated. Euclid's numbers "not having the ratio of a square number to a square
number" are here `4` and `3`.
-/
theorem proposition_10 (a : Length) :
    ∃ d e : Length,
      InSquareOnly a d ∧ ¬ CommensurableInSquare a e ∧ ¬ Commensurable a e := by
  -- let it be contrived that as `4` is to `3`, so the square on `a` to the square on `d`
  -- [Prop. 10.6 corr.]
  obtain ⟨f, d, -, hd⟩ := proposition_6_corollary 4 3 a
  -- the squares are commensurable [Prop. 10.6]
  have hsq : CommensurableInSquare a d := proposition_6 hd.symm (Area.divisible _ _)
  -- they do not have the ratio of a square number to a square number, since `4` and `3`
  -- do not: `a` is incommensurable in length with `d` [Prop. 10.9]
  have hlen : ¬ Commensurable a d := fun h => not_square_ratio (by
    obtain ⟨c, c', h'⟩ := proposition_9.mp h
    exact ⟨c, c', Elements.Book5.proposition_11 hd h'⟩)
  -- let `e` be the mean proportional of `a` and `d` [Prop. 6.13]: as `a` is to `d`, so
  -- the square on `a` to the square on `e` [Def. 5.9]
  obtain ⟨e, he⟩ := Length.mean a d
  obtain ⟨g, hg₁, hg₂⟩ := squaredRatio_sq a e
  have hgd : g = d :=
    Elements.Book5.proposition_9' (Elements.Book5.proposition_11 hg₁.symm he)
  subst hgd
  -- `a` is incommensurable in length with `d`, so the square on `a` with the square on
  -- `e` [Prop. 10.11]
  have hinsq : ¬ CommensurableInSquare a e :=
    (proposition_11 hg₂.symm Length.divisible Area.divisible).2 hlen
  exact ⟨g, e, ⟨hsq, hlen⟩, hinsq, fun h => hinsq (proposition_9_corollary h)⟩

end Elements.Book10
