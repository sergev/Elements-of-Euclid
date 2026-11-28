import Elements.Book7.Prop32

namespace Elements.Book7

/-- Euclid's argument: if `d` is the greatest common measure of `a`, `b`, `c`, the numbers
`e`, `f`, `g` it measures them by are the least in their ratio. -/
theorem least_of_greatest {a b c d e f g : ℕ} (hd : 0 < d) (he : 0 < e) (hae : a = e * d)
    (hbf : b = f * d) (hcg : c = g * d) (hgreat : ∀ k, k ∣ a → k ∣ b → k ∣ c → k ≤ d) :
    Least₃ e f g := by
  -- if not, there are numbers `h`, `k`, `l` less than `e`, `f`, `g` in the same ratio:
  -- the same parts `m` of some `x`, `y`, `z` as `e`, `f`, `g` are `n` of them
  rintro h k l - - - ⟨m, n, x, y, z, hm, -, rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨hlt, -, -⟩
  have hx : 0 < x := Nat.pos_of_ne_zero (by rintro rfl; rw [Nat.zero_mul] at he; omega)
  have hn : 1 < n := by
    have := Nat.lt_of_mul_lt_mul_left hlt
    omega
  -- `x` measures `a`, `b`, `c` according to the units in `M = n * d`, and `M` measures
  -- them according to the units in `x`, `y`, `z` [Prop. 7.16, associativity -- Missed by
  -- Euclid.]
  have hM : ∀ w, w * n * d = n * d * w := fun w => by ring
  -- `x` taken `n` times, and `x`, make `a` with `d` and `M`: as `x * n` is to `x`, so is
  -- `M` to `d` [Prop. 7.19]
  have h19 : x * n ∶ x ∷ n * d ∶ d :=
    (proposition_19 he hx (Nat.mul_pos (by omega) hd) hd).mpr (by ring)
  -- `x * n` is greater than `x`, so `M` is greater than `d` [Prop. 5.13]
  have hMd := lt_of_proportion he hx (Nat.mul_pos (by omega) hd) h19 (lt_mul hx hn)
  -- and `M` measures `a`, `b`, `c`: but `d` is the greatest that does
  have := hgreat (n * d) ⟨x, hae.trans (hM x)⟩ ⟨y, hbf.trans (hM y)⟩ ⟨z, hcg.trans (hM z)⟩
  omega

/-- To find the least of those numbers having the same ratio as any given numbers `a`,
`b`, `c`. -/
theorem proposition_33 {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∃ e f g, 0 < e ∧ 0 < f ∧ 0 < g ∧ SameRatio₃ e f g a b c ∧ Least₃ e f g := by
  -- `a`, `b`, `c` are prime to one another, and the unit alone measures them; or not, and
  -- their greatest common measure is `d` [Prop. 7.3]
  obtain ⟨d, hd, hda, hdb, hdc, hgreat⟩ :
      ∃ d, 0 < d ∧ d ∣ a ∧ d ∣ b ∧ d ∣ c ∧ ∀ k, k ∣ a → k ∣ b → k ∣ c → k ≤ d := by
    by_cases hp : PrimeTo₃ a b c
    · exact ⟨1, Nat.one_pos, unit_measures a, unit_measures b, unit_measures c,
        fun k hka hkb hkc => (hp k hka hkb hkc).le⟩
    · obtain ⟨d, hd1, hda, hdb, hdc, hg⟩ := proposition_3 ha hb hc hp
      exact ⟨d, by omega, hda, hdb, hdc, hg⟩
  -- as many times as `d` measures `a`, `b`, `c`, so many units are in `e`, `f`, `g`
  obtain ⟨e, rfl⟩ := hda
  obtain ⟨f, rfl⟩ := hdb
  obtain ⟨g, rfl⟩ := hdc
  have he : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; rw [Nat.mul_zero] at ha; omega)
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; rw [Nat.mul_zero] at hb; omega)
  have hg : 0 < g := Nat.pos_of_ne_zero (by rintro rfl; rw [Nat.mul_zero] at hc; omega)
  -- `e`, `f`, `g` measure `a`, `b`, `c` according to the units in `d` [Prop. 7.15]
  rw [proposition_16 he hd, proposition_16 hf hd, proposition_16 hg hd] at hgreat ⊢
  -- an equal number of times: they are in the same ratio [Def. 7.20]; and the least
  refine ⟨e, f, g, he, hf, hg, ⟨1, d, e, f, g, Nat.one_pos, hd, (Nat.mul_one e).symm, rfl,
    (Nat.mul_one f).symm, rfl, (Nat.mul_one g).symm, rfl⟩,
    least_of_greatest hd he rfl rfl rfl hgreat⟩

/-- The same for two numbers `a`, `b`: the least numbers `e`, `f` in their ratio. -/
theorem proposition_33' {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ∃ e f, 0 < e ∧ 0 < f ∧ e ∶ f ∷ a ∶ b ∧ Least e f := by
  -- the least `e`, `f`, `g` in the ratio of `a`, `b`, `b`: `f` and `g` are equal
  obtain ⟨e, f, g, he, hf, -, ⟨m, n, x, y, z, hm, hn, rfl, rfl, rfl, hby, rfl, hbz⟩,
    hl⟩ := proposition_33 ha hb hb
  obtain rfl : y = z := Nat.eq_of_mul_eq_mul_right hn (hby.symm.trans hbz)
  subst hby
  refine ⟨x * m, y * m, he, hf, ?_, fun h k hh hk hhk hlt => ?_⟩
  · -- `e`, `f` are the same parts of `a`, `b`: alternately, in the same ratio
    -- [Prop. 7.13]
    exact proposition_13 he ha hf hb
      (proportion_iff.mpr ⟨m, n, x, y, hm, hn, rfl, rfl, rfl, rfl⟩)
  · -- numbers `h`, `k` less than `e`, `f` in their ratio make `h`, `k`, `k` less than
    -- `e`, `f`, `f` in theirs [Prop. 7.13]
    obtain ⟨p, q, u, v, hp, hq, rfl, he', rfl, hf'⟩ :=
      proportion_iff.mp (proposition_13 hh hk he hf hhk)
    exact hl (u * p) (v * p) (v * p) hh hk hk ⟨p, q, u, v, v, hp, hq, rfl, he', rfl, hf',
      rfl, hf'⟩ ⟨hlt.1, hlt.2, hlt.2⟩

end Elements.Book7
