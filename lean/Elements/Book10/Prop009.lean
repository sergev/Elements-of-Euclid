import Elements.Book8
import Elements.Book10.Prop008

namespace Elements.Book10

open Elements.Book5 Elements.Book5.Magnitude Number

/-- Prop. 8.11 for numbers as magnitudes: between the squares on `c` and `d` falls a
number `x`, the squares and `x` continuously proportional in the ratio of `c` to `d`; so
square has to square the squared ratio of side to side. -/
theorem squares_squaredRatio (c d : ℕ+) :
    ∃ x : Number, Proportion ((c : Number) * c) x (c : Number) d ∧
      Proportion x ((d : Number) * d) (c : Number) d := by
  obtain ⟨-, x, hx, h₁, h₂⟩ := Elements.Book8.proposition_11 c.pos d.pos
  refine ⟨of x hx, number_proportion_iff.mpr ?_, number_proportion_iff.mpr ?_⟩ <;>
    simpa [val_mul] using ‹_›

/-- 10.9's first part: if `a` is to `b` as the number `c` to the number `d`, the square on
`a` is to the square on `b` as the square of `c` to the square of `d`: both are the
squared ratio of `c` to `d` [Props. 6.20 corr., 8.11]. -/
theorem proportion_squares {a b : Length} {c d : ℕ+}
    (h : Proportion a b (c : Number) (d : Number)) :
    Proportion (sq a) (sq b) ((c : Number) * c) ((d : Number) * d) := by
  -- the ratio of the square on `a` to the square on `b` is the squared ratio of `a` to
  -- `b` [Prop. 6.20 corr.]: as `a` to `e`, the third proportional
  obtain ⟨e, he₁, he₂⟩ := squaredRatio_sq a b
  -- and that of the square on `c` to the square on `d` the squared ratio of `c` to `d`
  -- [Prop. 8.11]
  obtain ⟨x, hx₁, hx₂⟩ := squares_squaredRatio c d
  -- so as the square on `a` is to the square on `b`, so the square on `c` to the square
  -- on `d` [Props. 5.11, 5.22]
  have h₁ : Proportion a b ((c : Number) * c) x :=
    Elements.Book5.proposition_11 h hx₁.symm
  have h₂ : Proportion b e x ((d : Number) * d) :=
    Elements.Book5.proposition_11 (Elements.Book5.proposition_11 he₁.symm h) hx₂.symm
  exact Elements.Book5.proposition_11 he₂ (Elements.Book5.proposition_22' h₁ h₂)

/--
Squares on lines commensurable in length have to one another the ratio which a square
number has to a square number; and squares having that ratio have sides commensurable in
length. Euclid's third and fourth parts, for lines incommensurable in length, are the
negations of both sides (`not_congr`).
-/
theorem proposition_9 {a b : Length} :
    Commensurable a b ↔ ∃ c d : ℕ+,
      Proportion (sq a) (sq b) ((c : Number) * c) ((d : Number) * d) := by
  constructor
  · -- `a` has to `b` the ratio which a number has to a number [Prop. 10.5]
    intro h
    obtain ⟨c, d, h⟩ := proposition_5 h
    exact ⟨c, d, proportion_squares h⟩
  · rintro ⟨c, d, h⟩
    -- both ratios are the squared ratios of `a` to `b` and of `c` to `d` [Props. 6.20
    -- corr., 8.11]: so as `a` is to `b`, so `c` to `d`. With `f` the line to which `a` is
    -- as `c` to `d` [Prop. 6.12], the square on `a` is to the square on `f` as the square
    -- on `c` to the square on `d`; so the squares on `f` and `b` are equal [Props. 5.11,
    -- 5.9], and `f` is `b`. -- Missed by Euclid.
    obtain ⟨f, hf⟩ := Length.fourth' (c : Number) (d : Number) a
    have h₁ := proportion_squares hf.symm
    have hfb : f = b :=
      sq_inj (Elements.Book5.proposition_9' (Elements.Book5.proposition_11 h₁ h.symm))
    subst hfb
    -- `a` is commensurable in length with `b` [Prop. 10.6]
    exact proposition_6 hf.symm (Length.divisible a c)

/-- 10.9, corollary: lines commensurable in length are always commensurable in square (but
not conversely: 10.10). -/
theorem proposition_9_corollary {a b : Length} (h : Commensurable a b) :
    CommensurableInSquare a b := by
  -- the squares have the ratio of a square number to a square number [Prop. 10.9], the
  -- ratio of a number to a number: they are commensurable [Prop. 10.6]
  obtain ⟨c, d, h⟩ := proposition_9.mp h
  have h' : Proportion (sq a) (sq b) ((c * c : ℕ+) : Number) ((d * d : ℕ+) : Number) := h
  exact proposition_6 h' (Area.divisible _ _)

end Elements.Book10
