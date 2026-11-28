import Elements.Book10.Prop047

namespace Elements.Book10

open Elements.Book5 Elements.Book7 Number

variable {ρ : Length}

/-- If `a ∶ b ∷ c ∶ d`, numbers, and `c`, `d` are not as a square number to a square
number, neither are `a`, `b` [Prop. 5.11]. -/
theorem not_square_ratio_of_proportion {a b c d : ℕ+}
    (h : Proportion (a : Number) (b : Number) (c : Number) (d : Number))
    (hns : ¬ ∃ p q : ℕ+, Proportion (c : Number) (d : Number) ((p : Number) * p)
      ((q : Number) * q)) :
    ¬ ∃ p q : ℕ+, Proportion (a : Number) (b : Number) ((p : Number) * p)
      ((q : Number) * q) :=
  fun ⟨p, q, h'⟩ => hns ⟨p, q, Elements.Book5.proposition_11 h.symm h'⟩

/-- If the numbers `m + k` and `k` are as the squares on `a` and `b`, and not as a square
number to a square number, then `a`, `b` are commensurable in square only [Props. 10.6,
10.9], `b` is the lesser [Prop. 5.14], and the square on `a` exceeds that on `b` by the
square on some `g`, with `m + k` to `m` as the square on `a` to the square on `g` [Prop.
5.19 corr.]: the steps of 10.48–10.53. -/
theorem terms_of_ratio {a b : Length} {m k : ℕ+}
    (h : Proportion ((m + k : ℕ+) : Number) (k : Number) (sq a) (sq b))
    (hns : ¬ ∃ c d : ℕ+, Proportion ((m + k : ℕ+) : Number) (k : Number)
      ((c : Number) * c)
      ((d : Number) * d)) :
    InSquareOnly a b ∧ b < a ∧ ∃ g, sq b + sq g = sq a ∧
      Proportion ((m + k : ℕ+) : Number) (m : Number) (sq a) (sq g) :=
  ⟨inSquareOnly_of_ratio h hns, conversion_squares h⟩

theorem sq_4 : SquareNumber ((4 : ℕ+) : ℕ) := ⟨2, by decide, rfl⟩
theorem sq_9 : SquareNumber ((9 : ℕ+) : ℕ) := ⟨3, by decide, rfl⟩
theorem sq_16 : SquareNumber ((16 : ℕ+) : ℕ) := ⟨4, by decide, rfl⟩
theorem sq_36 : SquareNumber ((36 : ℕ+) : ℕ) := ⟨6, by decide, rfl⟩

/-- To find a first binomial, relative to a rational line `r` laid out: the numbers `4`,
`12`, their sum `16` square, and `12` not [Prop. 10.28 lem. I]. -/
theorem proposition_48 {r : Length} (hr : Rational ρ r) : ∃ l, FirstBinomial ρ r l := by
  -- let `e` be commensurable in length with `r`: `r` itself; and let it be contrived that
  -- as `16` is to `12`, so the square on `r` to the square on `f` [Prop. 10.6 corr.]
  obtain ⟨-, f, -, hf⟩ := proposition_6_corollary (4 + 12) 12 r
  -- `r`, `f` are rational, commensurable in square only [Props. 10.6, 10.9]; via
  -- conversion, `16` is to `4` as the square on `r` to the square on `g` [Prop. 5.19
  -- corr.], so `r`, `g` are commensurable in length [Prop. 10.9]
  obtain ⟨hrf, hfr, g, hg, h₂⟩ := terms_of_ratio hf (not_square_ratio_of (Or.inl ⟨sq_16,
    by decide, not_square_of_between (k := 3) (by decide) (by decide)⟩))
  have hrg : Commensurable r g := proposition_9.mpr ⟨4, 2, h₂.symm⟩
  exact ⟨r + f, r, f, ⟨⟨hr, hr.of_inSquare hrf.1.symm, hrf, hfr⟩, ⟨g, hg, hrg.symm⟩,
    .refl r⟩, rfl⟩

end Elements.Book10
