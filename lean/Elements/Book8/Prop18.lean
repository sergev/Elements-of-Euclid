import Elements.Book8.Prop17

namespace Elements.Book8

open Elements.Book7

/-- Euclid's number for 8.18: for plane numbers `c * d`, `e * f` with `c ∶ d ∷ e ∶ f`,
`g = e * d` is in mean proportion, in the ratio of `c` to `e`, which is that of `d` to
`f`. -/
theorem similar_plane_mean {c d e f : ℕ} (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hf : 0 < f) (h : c ∶ d ∷ e ∶ f) :
    c * d ∶ e * d ∷ c ∶ e ∧ e * d ∶ e * f ∷ c ∶ e ∧ c ∶ e ∷ d ∶ f := by
  -- alternately, as `c` is to `e`, so `d` to `f` [Prop. 7.13]
  have halt := Elements.Book7.proposition_13 hc hd he hf h
  refine ⟨(Elements.Book7.proposition_17 hd hc he).symm, ?_, halt⟩
  -- `e` has made `g` by multiplying `d`, and `e * f` by multiplying `f` [Prop. 7.16]: as
  -- `d` is to `f`, so `g` to `e * f` [Prop. 7.17]
  rw [Elements.Book7.proposition_16 hd he, Elements.Book7.proposition_16 hf he]
  exact proportion_trans (Nat.mul_pos hd he) (Nat.mul_pos hf he) hd hf
    (Elements.Book7.proposition_17 he hd hf).symm halt.symm

/--
There exists one number in mean proportion to two similar plane numbers `c * d`, `e * f`
(`c ∶ d ∷ e ∶ f`, Def. 7.21), and plane has to plane the squared ratio of a corresponding
side to a corresponding side, `c` to `e` or `d` to `f`. The sides may be the unit: the
proof does not need more.
-/
theorem proposition_18 {c d e f : ℕ} (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (h : c ∶ d ∷ e ∶ f) :
    FallBetween 1 (c * d) (e * f) ∧ SquaredRatio (c * d) (e * f) c e ∧
      SquaredRatio (c * d) (e * f) d f := by
  -- let `d` make `g = e * d` by multiplying `e`: as `c` is to `e`, so `c * d` to `g`
  -- [Prop. 7.17], and so `g` to `e * f`
  obtain ⟨h₁, h₂, halt⟩ := similar_plane_mean hc hd he hf h
  have ha := Nat.mul_pos hc hd
  have hg := Nat.mul_pos he hd
  have hb := Nat.mul_pos he hf
  refine ⟨fallBetween_one ha hg hb (proportion_trans ha hg hc he h₁ h₂.symm),
    ⟨_, hg, h₁, h₂⟩, ⟨_, hg, ?_, ?_⟩⟩
  · exact proportion_trans ha hg hc he h₁ halt
  · exact proportion_trans hg hb hc he h₂ halt

end Elements.Book8
