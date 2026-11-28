import Elements.Book7.Prop35

namespace Elements.Book7

/-- To find the least number that three given numbers `a`, `b`, `c` measure. -/
theorem proposition_36 {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∃ d, LeastMeasured₃ d a b c := by
  -- the least number `d` that `a` and `b` measure [Prop. 7.34]
  obtain ⟨d, hd⟩ := proposition_34 ha hb
  obtain ⟨hd0, had, hbd, -⟩ := id hd
  by_cases hcd : c ∣ d
  · -- `c` measures `d`: `a`, `b`, `c` measure `d`
    refine ⟨d, hd0, had, hbd, hcd, fun e he hae hbe _ => ?_⟩
    -- a number `e` less than `d` that they measure is measured by `d` [Prop. 7.35]
    exact le_of_measures he (proposition_35 hd hae hbe)
  · -- the least number `e` that `c` and `d` measure [Prop. 7.34]
    obtain ⟨e, he⟩ := proposition_34 hc hd0
    obtain ⟨he0, hce, hde, -⟩ := id he
    -- `a`, `b` measure `d`, which measures `e`; and `c` measures `e`
    refine ⟨e, he0, measures_trans had hde, measures_trans hbd hde, hce,
      fun f hf haf hbf hcf => ?_⟩
    -- a number `f` less than `e` that they measure is measured by `d` [Prop. 7.35], and
    -- by `c`, so by `e` [Prop. 7.35]
    exact le_of_measures hf (proposition_35 he hcf (proposition_35 hd haf hbf))

end Elements.Book7
