import Elements.Book7.Prop02

namespace Elements.Book7

/-- To find the greatest common measure of three numbers `a`, `b`, `c` not prime to one
another. -/
theorem proposition_3 {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : ¬ PrimeTo₃ a b c) : ∃ g, 1 < g ∧ GreatestCommonMeasure₃ g a b c := by
  -- some number `k` measures `a`, `b` and `c`
  simp only [PrimeTo₃, not_forall] at h
  obtain ⟨k, hka, hkb, hkc, hk⟩ := h
  have hk1 : 1 < k := by
    have := Nat.pos_of_dvd_of_pos hka ha
    omega
  -- the greatest common measure `d` of `a`, `b` [Prop. 7.2]
  obtain ⟨d, -, hd⟩ := proposition_2 ha hb fun h' => hk (h' k hka hkb)
  have hda := hd.1
  have hdb := hd.2.1
  have hdpos := Nat.pos_of_dvd_of_pos hda ha
  by_cases hdc : d ∣ c
  · -- `d` measures `c`: it is a common measure of `a`, `b`, `c`
    refine ⟨d, Nat.lt_of_lt_of_le hk1 (le_of_measures hdpos
      (proposition_2_corollary ha hb hd hka hkb)), hda, hdb, hdc, fun e hea heb _ => ?_⟩
    -- a greater `e` measuring `a`, `b`, `c` measures `d` [Prop. 7.2 corr.]: impossible
    exact le_of_measures hdpos (proposition_2_corollary ha hb hd hea heb)
  · -- `c` and `d` are not prime to one another: `k` measures `d` [Prop. 7.2 corr.]
    have hkd := proposition_2_corollary ha hb hd hka hkb
    -- their greatest common measure `e` [Prop. 7.2]
    obtain ⟨e, he1, he⟩ := proposition_2 hdpos hc fun h' => by
      have := h' k hkd hkc
      omega
    -- `e` measures `d`, so `a` and `b`; and it measures `c`
    refine ⟨e, he1, measures_trans he.1 hda, measures_trans he.1 hdb, he.2.1,
      fun f hfa hfb hfc => ?_⟩
    -- a greater `f` measuring `a`, `b`, `c` measures `d`, so `e` [Prop. 7.2 corr.]
    have hfd := proposition_2_corollary ha hb hd hfa hfb
    exact le_of_measures (Nat.pos_of_dvd_of_pos he.1 hdpos)
      (proposition_2_corollary hdpos hc he hfd hfc)

end Elements.Book7
