import Elements.Book8.Prop20

namespace Elements.Book8

open Elements.Book7

/--
If two numbers fall between two numbers in mean proportion, the latter are similar solid
numbers: `p * q * r` and `s * t * u` with `p ∶ q ∷ s ∶ t` and `q ∶ r ∷ t ∶ u`
(Def. 7.21). As in 8.20, the sides may be the unit (`2`, `4`, `8`, `16`).
-/
theorem proposition_21 {a b : ℕ} (hab : FallBetween 2 a b) :
    ∃ p q r s t u, 0 < p ∧ 0 < q ∧ 0 < r ∧ 0 < s ∧ 0 < t ∧ 0 < u ∧
      a = p * q * r ∧ b = s * t * u ∧ p ∶ q ∷ s ∶ t ∧ q ∶ r ∷ t ∶ u := by
  obtain ⟨ha, hb, c, d, hc, hd, h₁, h₂⟩ := hab.two
  -- let the three least numbers `e`, `f`, `g` having the same ratio as `a`, `c`, `d` be
  -- taken [Props. 7.33, 8.2]
  obtain ⟨x, y, hx, hy, hxy, hl⟩ := Elements.Book7.proposition_33' ha hc
  obtain ⟨hP, hPin, hPl⟩ := proposition_2 hx hy hl 2
  have hef : powers x y 2 0 ∶ powers x y 2 1 ∷ x ∶ y := hPin 0
  have hfg : powers x y 2 1 ∶ powers x y 2 2 ∷ x ∶ y := hPin 1
  have he : 0 < powers x y 2 0 := hP 0
  have hf : 0 < powers x y 2 1 := hP 1
  have hg : 0 < powers x y 2 2 := hP 2
  -- the outermost, `e` and `g`, are prime to one another [Prop. 8.3]
  have hprime : PrimeTo (powers x y 2 0) (powers x y 2 2) :=
    proposition_3 hP (hPin.continued hP hx hy) hPl
  generalize powers x y 2 0 = e at hef hprime he
  generalize powers x y 2 1 = f at hef hfg hf
  generalize powers x y 2 2 = g at hfg hprime hg
  -- `e`, `f`, `g` are in the ratio of `a` to `c`, which is that of `c` to `d` and `d` to
  -- `b`
  have hac : e ∶ f ∷ a ∶ c := proportion_trans he hf hx hy hef hxy
  have hcd : f ∶ g ∷ c ∶ d := proportion_trans hf hg hx hy hfg
    (proportion_trans hx hy ha hc hxy h₁)
  have hcd' : e ∶ f ∷ c ∶ d := proportion_trans he hf ha hc hac h₁
  have hdb : f ∶ g ∷ d ∶ b := proportion_trans hf hg hc hd hcd h₂
  -- one number, `f`, falls between `e` and `g`: they are similar plane numbers, `h * k`
  -- and `l * m`, continuously proportional in the ratio of `h` to `l` [Prop. 8.20]
  obtain ⟨h, k, l, m, hh, hk, hl, hm, rfl, -, rfl, hhk, hhl⟩ :=
    plane_of_mean he hf hg (proportion_trans he hf hc hd hcd' hcd.symm)
  -- via equality, as `e` is to `g`, so `a` to `d`, and `c` to `b` [Prop. 7.14]
  have had := Elements.Book7.proposition_14' he hf hg ha hc hd hac hcd
  have hcb := Elements.Book7.proposition_14' he hf hg hc hd hb hcd' hdb
  -- `e`, `g` are prime, so the least [Prop. 7.21]: `e` measures `a` as many times, `n`,
  -- as `g` measures `d`, and `c` as many times, `o`, as `g` measures `b` [Prop. 7.20]
  have hleast := Elements.Book7.proposition_21 he hg hprime
  obtain ⟨n, rfl, -⟩ := Elements.Book7.proposition_20 ha hd he hg hleast had
  obtain ⟨o, rfl, rfl⟩ := Elements.Book7.proposition_20 hc hb he hg hleast hcb
  have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; rw [Nat.mul_zero] at ha; omega)
  have ho : 0 < o := Nat.pos_of_ne_zero (by rintro rfl; rw [Nat.mul_zero] at hc; omega)
  -- `n`, `o` have made `a`, `c` by multiplying `e`: as `n` is to `o`, so `a` to `c`
  -- [Prop. 7.18], that is, `e` to `f`, and so `h` to `l`
  have hno : n ∶ o ∷ h ∶ l := proportion_trans hn ho ha hc
    (Elements.Book7.proposition_18 hn ho he)
    (proportion_trans ha hc he hf hac.symm hhl.symm)
  -- and as `h` is to `l`, so `k` to `m` [Prop. 7.13]
  have hkm := Elements.Book7.proposition_13 hh hk hl hm hhk
  -- so, alternately, `k ∶ n ∷ m ∶ o` [Prop. 7.13]
  refine ⟨h, k, n, l, m, o, hh, hk, hn, hl, hm, ho, rfl, rfl, hhk, ?_⟩
  exact Elements.Book7.proposition_13 hk hm hn ho
    (proportion_trans hk hm hh hl hkm.symm hno.symm)

end Elements.Book8
