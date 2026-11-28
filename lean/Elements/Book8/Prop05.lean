import Elements.Book8.Prop04

namespace Elements.Book8

open Elements.Book7

/--
Plane numbers `c * d` and `e * f` have to one another the ratio compounded out of the
ratios of their sides, `c` to `e` and `d` to `f`. Euclid takes the least numbers
continuously proportional in those ratios (8.4); 8.4 asks for the ratios in least numbers,
which are taken first [Prop. 7.33]. -- Missed by Euclid. The sides may be the unit: the
proof does not need more.
-/
theorem proposition_5 {c d e f : ℕ} (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf : 0 < f) :
    CompoundRatio (c * d) (e * f) c e d f := by
  -- the ratios of `c` to `e` and `d` to `f`, in least numbers [Prop. 7.33]
  obtain ⟨c', e', hc', he', hce, hlce⟩ := Elements.Book7.proposition_33' hc he
  obtain ⟨d', f', hd', hf', hdf, hldf⟩ := Elements.Book7.proposition_33' hd hf
  -- let the least numbers `g`, `h`, `k`, continuously proportional in those ratios, be
  -- taken [Prop. 8.4]
  obtain ⟨s, hs, hrat, -⟩ := proposition_4 (n := 2)
    (p := fun i => if i.val = 0 then c' else d')
    (q := fun i => if i.val = 0 then e' else f')
    (fun i => by split <;> assumption) (fun i => by split <;> assumption)
    (fun i => by split <;> assumption)
  have hgh : s 0 ∶ s 1 ∷ c ∶ e :=
    proportion_trans (hs 0) (hs 1) hc' he' (hrat 0) hce
  have hhk : s 1 ∶ s 2 ∷ d ∶ f :=
    proportion_trans (hs 1) (hs 2) hd' hf' (hrat 1) hdf
  refine ⟨s 0, s 1, s 2, hs 0, hs 1, hs 2, hgh, hhk, ?_⟩
  -- `d` multiplying `c` and `e` makes `c * d` and `l = e * d`: as `c` is to `e`, so
  -- `c * d` is to `l` [Prop. 7.17], and so `g` to `h`
  have h₁ : s 0 ∶ s 1 ∷ c * d ∶ e * d := proportion_trans (hs 0) (hs 1) hc he hgh
    (Elements.Book7.proposition_17 hd hc he)
  -- `e` multiplying `d` makes `l` [Prop. 7.16], and multiplying `f` makes `e * f`
  -- [Prop. 7.16]: as `d` is to `f`, so `l` is to `e * f` [Prop. 7.17], and so `h` to `k`
  have h₂ : s 1 ∶ s 2 ∷ e * d ∶ e * f := by
    rw [Elements.Book7.proposition_16 hd he, Elements.Book7.proposition_16 hf he]
    exact proportion_trans (hs 1) (hs 2) hd hf hhk
      (Elements.Book7.proposition_17 he hd hf)
  -- via equality, as `g` is to `k`, so `c * d` to `e * f` [Prop. 7.14]
  exact (Elements.Book7.proposition_14' (hs 0) (hs 1) (hs 2) (Nat.mul_pos hc hd)
    (Nat.mul_pos he hd) (Nat.mul_pos he hf) h₁ h₂).symm

end Elements.Book8
