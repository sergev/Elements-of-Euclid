import Elements.Book7.Prop33

namespace Elements.Book7

/-- If `b ∶ e ∷ c ∶ d` and `b` measures `e`, then `c` measures `d` [Prop. 7.19]. -/
theorem measures_of_proportion {b c d e : ℕ} (hb : 0 < b) (he : 0 < e) (hc : 0 < c)
    (hd : 0 < d) (h : b ∶ e ∷ c ∶ d) (hbe : b ∣ e) : c ∣ d := by
  obtain ⟨n, rfl⟩ := hbe
  rw [proposition_19 hb he hc hd] at h
  -- `d * b = c * (b * n)` [Prop. 7.16, associativity -- Missed by Euclid.]
  exact ⟨n, Nat.eq_of_mul_eq_mul_right hb (by rw [h]; ring)⟩

/-- To find the least number `c` that two given numbers `a`, `b` measure. -/
theorem proposition_34 {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ∃ c, LeastMeasured c a b := by
  by_cases hp : PrimeTo a b
  · -- prime to one another: let `a` multiplying `b` make `c`; `b` multiplying `a` makes
    -- `c` too [Prop. 7.16], so `a` and `b` measure `c`
    refine ⟨b * a, Nat.mul_pos hb ha, ⟨b, proposition_16 ha hb⟩, ⟨a, rfl⟩,
      fun d hd ⟨e, hde⟩ ⟨f, hdf⟩ => ?_⟩
    -- if not least, they measure some `d` less than `c`, `e` and `f` times
    by_contra hlt
    have he : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; rw [Nat.mul_zero] at hde; omega)
    have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; rw [Nat.mul_zero] at hdf; omega)
    -- `a` multiplying `e`, and `b` multiplying `f`, make `d`: `a ∶ b ∷ f ∶ e`
    -- [Prop. 7.19]
    have h₁ : a ∶ b ∷ f ∶ e := by
      rw [proposition_19 ha hb hf he, proposition_16 ha he, proposition_16 hb hf, ← hde,
        ← hdf]
    -- `a`, `b` are the least in their ratio [Prop. 7.21]: `b` measures `e` [Prop. 7.20]
    obtain ⟨n, -, hen⟩ := proposition_20 hf he ha hb (proposition_21 ha hb hp) h₁
    -- `a` multiplying `b` and `e` makes `c` and `d`: `b ∶ e ∷ c ∶ d` [Prop. 7.17]
    have h₂ := proposition_17 ha hb he
    rw [proposition_16 ha he, ← hde] at h₂
    -- `b` measures `e`, so `c` measures `d`, the greater the lesser: impossible
    exact not_measures_of_lt hd (by omega)
      (measures_of_proportion hb he (Nat.mul_pos hb ha) hd h₂ ⟨n, hen⟩)
  · -- not prime to one another: the least `f`, `e` in the ratio of `a`, `b` [Prop. 7.33]
    obtain ⟨f, e, hf, he, hfe, hl⟩ := proposition_33' ha hb
    -- `a * e = b * f` [Prop. 7.19]: let `a` multiplying `e` make `c`; `b` multiplying `f`
    -- makes `c`
    have hc : e * a = f * b := by
      rw [proposition_16 ha he, proposition_16 hb hf]
      exact ((proposition_19 hf he ha hb).mp hfe).symm
    refine ⟨e * a, Nat.mul_pos he ha, ⟨e, proposition_16 ha he⟩,
      ⟨f, hc.trans (proposition_16 hb hf)⟩, fun d hd ⟨g, hdg⟩ ⟨h, hdh⟩ => ?_⟩
    -- if not least, they measure some `d` less than `c`, `g` and `h` times
    by_contra hlt
    have hg : 0 < g := Nat.pos_of_ne_zero (by rintro rfl; rw [Nat.mul_zero] at hdg; omega)
    have hh : 0 < h := Nat.pos_of_ne_zero (by rintro rfl; rw [Nat.mul_zero] at hdh; omega)
    -- `a` multiplying `g`, and `b` multiplying `h`, make `d`: `a ∶ b ∷ h ∶ g`
    -- [Prop. 7.19]
    have h₁ : a ∶ b ∷ h ∶ g := by
      rw [proposition_19 ha hb hh hg, proposition_16 ha hg, proposition_16 hb hh, ← hdg,
        ← hdh]
    -- and `f ∶ e ∷ h ∶ g` -- Missed by Euclid.
    have h₂ := proportion_trans hf he ha hb hfe h₁
    -- `f`, `e` are the least: `e` measures `g` [Prop. 7.20]
    obtain ⟨n, -, hgn⟩ := proposition_20 hh hg hf he hl h₂
    -- `a` multiplying `e` and `g` makes `c` and `d`: `e ∶ g ∷ c ∶ d` [Prop. 7.17]
    have h₃ := proposition_17 ha he hg
    rw [proposition_16 ha hg, ← hdg] at h₃
    -- `e` measures `g`, so `c` measures `d`, the greater the lesser: impossible
    exact not_measures_of_lt hd (by omega)
      (measures_of_proportion he hg (Nat.mul_pos he ha) hd h₃ ⟨n, hgn⟩)

end Elements.Book7
