import Elements.Book8.Prop10

namespace Elements.Book8

open Elements.Book7

/-- Euclid's numbers for 8.11: `c * c`, `d * c`, `d * d` are continuously proportional in
the ratio of `c` to `d` [Props. 7.17, 7.18]. -/
theorem squares_continued {c d : ℕ} (hc : 0 < c) (hd : 0 < d) :
    c * c ∶ d * c ∷ c ∶ d ∧ d * c ∶ d * d ∷ c ∶ d :=
  ⟨(Elements.Book7.proposition_17 hc hc hd).symm,
    (Elements.Book7.proposition_18 hc hd hd).symm⟩

/--
There exists one number in mean proportion to two square numbers `c * c`, `d * d`, and
square has to square the squared ratio of side `c` to side `d`. The sides may be the
unit: the proof does not need more.
-/
theorem proposition_11 {c d : ℕ} (hc : 0 < c) (hd : 0 < d) :
    FallBetween 1 (c * c) (d * d) ∧ SquaredRatio (c * c) (d * d) c d := by
  -- let `c` make `e = d * c` by multiplying `d`: `c` has made `c * c`, `e` by multiplying
  -- `c`, `d`, so as `c` is to `d`, so `c * c` to `e` [Prop. 7.17]; and so `e` to `d * d`
  -- [Prop. 7.18]
  obtain ⟨h₁, h₂⟩ := squares_continued hc hd
  have he : 0 < d * c := Nat.mul_pos hd hc
  refine ⟨fallBetween_one (Nat.mul_pos hc hc) he (Nat.mul_pos hd hd)
    (proportion_trans (Nat.mul_pos hc hc) he hc hd h₁ h₂.symm), d * c, he, h₁, h₂⟩

end Elements.Book8
