import Elements.Book10.Prop028

namespace Elements.Book10

open Elements.Book5 Elements.Book7 Number

variable {ρ : Length}

/-- Prop. 5.19, corollary (via conversion), for numbers and areas: from `(a + b) ∶ b ∷
(c + d) ∶ d`, separating [Prop. 5.17], inversely [Prop. 5.7 corr.], and composing [Prop.
5.18]. -/
theorem convertendo {a b : Number} {c d : Area} (h : Proportion (a + b) b (c + d) d) :
    Proportion (a + b) a (c + d) c := by
  have h₁ := Elements.Book5.proposition_7_corollary (Elements.Book5.proposition_17 h)
  have h₂ := Elements.Book5.proposition_18 h₁ (Area.fourth' _ _ _)
  rwa [add_comm b a, add_comm d c] at h₂

/-- If the numbers `m + k` and `k` are as the squares on `a` and `f`, the square on `a`
exceeds the square on `f` by the square on some `g`, and `m + k` is to `m` as the square
on `a` to the square on `g`: `f` is less than `a`, the semicircle on `a` with `f` fitted
in it [Props. 3.31, 1.47], and via conversion [Prop. 5.19 corr.]. -/
theorem conversion_squares {a f : Length} {m k : ℕ+}
    (h : Proportion ((m + k : ℕ+) : Number) (k : Number) (sq a) (sq f)) :
    f < a ∧ ∃ g, sq f + sq g = sq a ∧
      Proportion ((m + k : ℕ+) : Number) (m : Number) (sq a) (sq g) := by
  have hfa : f < a := sq_lt_sq.mp ((h.gt 1 1).mp (val_lt.mp (by
    simp only [Magnitude.one_mult, val_coe, PNat.add_coe]; have := m.pos; omega)))
  obtain ⟨g, hg⟩ := Length.exceeds hfa
  refine ⟨hfa, g, hg, ?_⟩
  have e₁ : sq a = sq g + sq f := by rw [← hg, add_comm]
  have e₂ : ((m + k : ℕ+) : Number) = (m : Number) + k := rfl
  rw [e₁, e₂] at h ⊢
  exact convertendo h

/-- To find two rational lines commensurable in square only, the square on the greater
exceeding the square on the lesser by the square on a line commensurable in length with
the greater. -/
theorem proposition_29 : ∃ x y, BinomialTerms ρ x y ∧ ExceedsComm x y := by
  -- two square numbers `16` and `4`, their difference `12` not square [Prop. 10.28 lem.
  -- I, with `6` and `2`, not similar plane numbers]
  have h₁ := (proposition_28_lemma_1 (a := 6) (b := 2) (d := 2) rfl).1
  have h12 : ¬ SquareNumber 12 := not_square_of_between (k := 3) (by decide) (by decide)
  -- let the rational `a` be laid down, and let it be contrived that as `16` is to `12`,
  -- so the square on `a` to the square on `f` [Prop. 10.6 corr.]
  obtain ⟨-, f, -, hf⟩ := proposition_6_corollary (4 + 12) 12 ρ
  -- the squares are commensurable [Prop. 10.6], so `f` is rational; `16` is not to `12`
  -- as a square number to a square number, so `a`, `f` are incommensurable in length
  -- [Prop. 10.9]
  have haf := inSquareOnly_of_ratio hf (not_square_ratio_of (Or.inl
    ⟨⟨4, by decide, by rw [← h₁]; rfl⟩, by decide, h12⟩))
  have hfr : Rational ρ f := Rational.of_inSquare (Rational.self ρ) haf.1.symm
  -- via conversion, as `16` is to `4`, so the square on `a` to the square on `g`, the
  -- line by which the square on `a` exceeds the square on `f` [Props. 5.19 corr., 3.31,
  -- 1.47]
  obtain ⟨hfa, g, hg, h₂⟩ := conversion_squares hf
  -- that is the ratio of a square number to a square number: `a`, `g` are commensurable
  -- in length [Prop. 10.9]
  have hag : Commensurable ρ g := proposition_9.mpr ⟨4, 2, h₂.symm⟩
  exact ⟨ρ, f, ⟨Rational.self ρ, hfr, haf, hfa⟩, g, hg, hag.symm⟩

end Elements.Book10
