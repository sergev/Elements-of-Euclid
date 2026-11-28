import Elements.Book8.Prop18

namespace Elements.Book8

open Elements.Book7

/--
Two numbers fall between two similar solid numbers `c * d * e`, `f * g * h`
(`c ∶ d ∷ f ∶ g` and `d ∶ e ∷ g ∶ h`, Def. 7.21) in mean proportion, and solid has to
solid the cubed ratio of a corresponding side to a corresponding side, `c` to `f`, `d` to
`g`, and `e` to `h`. The sides may be the unit.
-/
theorem proposition_19 {c d e f g h : ℕ} (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hf : 0 < f) (hg : 0 < g) (hh : 0 < h) (h₁ : c ∶ d ∷ f ∶ g) (h₂ : d ∶ e ∷ g ∶ h) :
    FallBetween 2 (c * d * e) (f * g * h) ∧ CubedRatio (c * d * e) (f * g * h) c f ∧
      CubedRatio (c * d * e) (f * g * h) d g ∧
      CubedRatio (c * d * e) (f * g * h) e h := by
  -- `k = c * d`, `l = f * g` are similar plane numbers, and `m = f * d` is in mean
  -- proportion, in the ratio of `c` to `f`, which is that of `d` to `g` [Prop. 8.18]
  obtain ⟨hkm, hml, hcd⟩ := similar_plane_mean hc hd hf hg h₁
  -- alternately, as `d` is to `g`, so `e` to `h` [Prop. 7.13]
  have hde := Elements.Book7.proposition_13 hd he hg hh h₂
  have hk := Nat.mul_pos hc hd
  have hm := Nat.mul_pos hf hd
  have hl := Nat.mul_pos hf hg
  have ha := Nat.mul_pos hk he
  have hn := Nat.mul_pos hm he
  have ho := Nat.mul_pos hm hh
  have hb := Nat.mul_pos hl hh
  have hce := proportion_trans hc hf hd hg hcd hde
  -- let `e`, `h` make `n`, `o` by multiplying `m`
  -- `e` has made `c * d * e`, `n` by multiplying `k`, `m`: as `k` is to `m`, so they
  -- [Prop. 7.17]
  have han : c * d * e ∶ f * d * e ∷ c ∶ f := proportion_trans ha hn hk hm
    (Elements.Book7.proposition_17 he hk hm).symm hkm
  -- `e`, `h` have made `n`, `o` by multiplying `m` [Prop. 7.18]
  have hno : f * d * e ∶ f * d * h ∷ c ∶ f := proportion_trans hn ho he hh
    (Elements.Book7.proposition_18 he hh hm).symm hce.symm
  -- `h` has made `o`, `f * g * h` by multiplying `m`, `l` [Prop. 7.17]
  have hob : f * d * h ∶ f * g * h ∷ c ∶ f := proportion_trans ho hb hm hl
    (Elements.Book7.proposition_17 hh hm hl).symm hml
  refine ⟨fallBetween_two ha hn ho hb (proportion_trans ha hn hc hf han hno.symm)
    (proportion_trans hn ho hc hf hno hob.symm), ⟨_, _, hn, ho, han, hno, hob⟩, ?_, ?_⟩
  · exact ⟨_, _, hn, ho, proportion_trans ha hn hc hf han hcd,
      proportion_trans hn ho hc hf hno hcd, proportion_trans ho hb hc hf hob hcd⟩
  · exact ⟨_, _, hn, ho, proportion_trans ha hn hc hf han hce,
      proportion_trans hn ho hc hf hno hce, proportion_trans ho hb hc hf hob hce⟩

end Elements.Book8
