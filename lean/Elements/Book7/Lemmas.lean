import Elements.Book7.Definitions
import Mathlib.Tactic.Ring

/-
What Euclid takes for granted in Book 7: the common notions of measuring, and Book 5's
propositions on proportion, used of numbers.
-/

namespace Elements.Book7

/-! The common notions of measuring (Fitzpatrick's notes to 7.1). -/

/-- If `a` measures `b`, and `b` measures `c`, then `a` measures `c`: `b` taken `l` times
is `a` taken `k` times, `l` times over. -/
theorem measures_trans {a b c : ℕ} (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  obtain ⟨k, rfl⟩ := hab
  obtain ⟨l, rfl⟩ := hbc
  induction l with
  | zero => exact ⟨0, rfl⟩
  | succ l ih =>
    obtain ⟨j, hj⟩ := ih
    exact ⟨j + k, by rw [Nat.mul_succ, hj, Nat.mul_add]⟩

/-- If `a` measures the whole `b` and a part `c` taken away, it measures the remainder. -/
theorem measures_sub {a b c : ℕ} (hb : a ∣ b) (hc : a ∣ c) : a ∣ b - c := by
  obtain ⟨k, rfl⟩ := hb
  obtain ⟨l, rfl⟩ := hc
  exact ⟨k - l, (Nat.mul_sub a k l).symm⟩

/-- If `a` measures `b` and `c`, it measures the whole `b + c`. -/
theorem measures_add {a b c : ℕ} (hb : a ∣ b) (hc : a ∣ c) : a ∣ b + c := by
  obtain ⟨k, rfl⟩ := hb
  obtain ⟨l, rfl⟩ := hc
  exact ⟨k + l, (Nat.mul_add a k l).symm⟩

/-- A number measures itself, once. -/
theorem measures_self (a : ℕ) : a ∣ a := ⟨1, (Nat.mul_one a).symm⟩

/-- The unit measures every number, according to the units in it. -/
theorem unit_measures (a : ℕ) : 1 ∣ a := ⟨a, (Nat.one_mul a).symm⟩

/-- The greater does not measure the lesser. -/
theorem not_measures_of_lt {a b : ℕ} (hb : 0 < b) (h : b < a) : ¬ a ∣ b := by
  rintro ⟨k, rfl⟩
  rcases k with _ | k
  · omega
  · rw [Nat.mul_succ] at h
    omega

/-- The measure is not greater than the number it measures. -/
theorem le_of_measures {a b : ℕ} (hb : 0 < b) (h : a ∣ b) : a ≤ b :=
  Nat.le_of_not_lt fun hab => not_measures_of_lt hb hab h

/-- All of any multitude of numbers are a number. -/
theorem sum_pos {n : ℕ} {a : Fin (n + 1) → ℕ} (ha : ∀ i, 0 < a i) : 0 < sum a := by
  induction n with
  | zero => exact ha 0
  | succ n ih =>
    have := ih (a := fun i => a i.castSucc) fun i => ha _
    simp only [sum]
    omega

/-- `n + 1` numbers each equal to `x` are `x` taken `n + 1` times. -/
theorem sum_const (x : ℕ) {n : ℕ} : sum (fun _ : Fin (n + 1) => x) = x * (n + 1) := by
  induction n with
  | zero => exact (Nat.mul_one x).symm
  | succ n ih =>
    simp only [sum]
    rw [ih, Nat.mul_succ x (n + 1)]

/-! The process of 7.1 and 7.2. -/

/--
Two numbers, the lesser subtracted continually, in turn, from the greater (7.1, 7.2): the
remainder at which the process stops, being equal to the number before it, which it
measures. It is the unit in 7.1, and the greatest common measure in 7.2. A number
measuring the one before it is subtracted from it until it is used up; so the last
remainder measures the one before it exactly when it is the last subtracted.
-/
def remainder (a b : ℕ) : ℕ :=
  if a = 0 then b else if b = 0 then a
  else if a < b then remainder a (b - a)
  else if b < a then remainder (a - b) b
  else a
termination_by a + b
decreasing_by all_goals omega

/-- The remainder of two numbers is a number, or the unit. -/
theorem remainder_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : 0 < remainder a b := by
  fun_induction remainder a b <;> omega

/-! The four cases of Def. 7.20 at once. -/

/--
`a ∶ b ∷ c ∶ d` exactly when `a`, `b` are some `e` taken `m` and `n` times, and `c`, `d`
are some `f` taken as many times. This is Def. 7.20 and nothing more: the same multiple is
`n = 1`, the same part `m = 1`, the same parts `1 < m < n` (or `1 < n < m`, the other way
round), and equals `m = n`.

The choice of `m`, `n` matters: `4 ∶ 6` is `2` taken `2` and `3` times, and the unit `4`
and `6` times, but `2 ∶ 3` only the first. So the definition alone does not give that
ratios equal to the same ratio are equal to one another (`proportion_trans`).
-/
theorem proportion_iff {a b c d : ℕ} :
    a ∶ b ∷ c ∶ d ↔
      ∃ m n e f, 0 < m ∧ 0 < n ∧ a = e * m ∧ b = e * n ∧ c = f * m ∧ d = f * n := by
  constructor
  · rintro (⟨n, hn, rfl, rfl⟩ | ⟨n, ⟨hn, rfl⟩, ⟨-, rfl⟩⟩ |
      ⟨m, n, ⟨hm, hmn, e, rfl, rfl⟩, ⟨-, -, f, rfl, rfl⟩⟩ |
      ⟨m, n, ⟨hm, hmn, e, rfl, rfl⟩, ⟨-, -, f, rfl, rfl⟩⟩)
    · exact ⟨n, 1, b, d, hn, Nat.one_pos, rfl, (Nat.mul_one b).symm, rfl,
        (Nat.mul_one d).symm⟩
    · exact ⟨1, n, a, c, Nat.one_pos, by omega, (Nat.mul_one a).symm, rfl,
        (Nat.mul_one c).symm, rfl⟩
    · exact ⟨m, n, e, f, by omega, by omega, rfl, rfl, rfl, rfl⟩
    · exact ⟨n, m, e, f, by omega, by omega, rfl, rfl, rfl, rfl⟩
  · rintro ⟨m, n, e, f, hm, hn, rfl, rfl, rfl, rfl⟩
    rcases Nat.lt_trichotomy m n with h | rfl | h
    · rcases Nat.lt_or_ge 1 m with h1 | h1
      · exact Or.inr (Or.inr (Or.inl ⟨m, n, ⟨h1, h, e, rfl, rfl⟩, ⟨h1, h, f, rfl, rfl⟩⟩))
      · obtain rfl : m = 1 := by omega
        rw [Nat.mul_one, Nat.mul_one]
        exact Or.inr (Or.inl ⟨n, ⟨h, rfl⟩, ⟨h, rfl⟩⟩)
    · exact Or.inl ⟨1, Nat.one_pos, (Nat.mul_one _).symm, (Nat.mul_one _).symm⟩
    · rcases Nat.lt_or_ge 1 n with h1 | h1
      · exact Or.inr (Or.inr (Or.inr ⟨n, m, ⟨h1, h, e, rfl, rfl⟩, ⟨h1, h, f, rfl, rfl⟩⟩))
      · obtain rfl : n = 1 := by omega
        rw [Nat.mul_one, Nat.mul_one]
        exact Or.inl ⟨m, hm, rfl, rfl⟩

/-- If as the first is to the second, so the third is to the fourth, then as the third is
to the fourth, so the first is to the second (Def. 7.20). -/
theorem Proportion.symm {a b c d : ℕ} (h : a ∶ b ∷ c ∶ d) : c ∶ d ∷ a ∶ b := by
  obtain ⟨m, n, e, f, hm, hn, rfl, rfl, rfl, rfl⟩ := proportion_iff.mp h
  exact proportion_iff.mpr ⟨m, n, f, e, hm, hn, rfl, rfl, rfl, rfl⟩

/-- Inversely: as the second is to the first, so the fourth to the third (Def. 7.20). -/
theorem Proportion.inv {a b c d : ℕ} (h : a ∶ b ∷ c ∶ d) : b ∶ a ∷ d ∶ c := by
  obtain ⟨m, n, e, f, hm, hn, rfl, rfl, rfl, rfl⟩ := proportion_iff.mp h
  exact proportion_iff.mpr ⟨n, m, e, f, hn, hm, rfl, rfl, rfl, rfl⟩

/-- Two numbers are as themselves: each is as many units as it has (Def. 7.20, the unit
being a part of each). -/
theorem Proportion.refl {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : a ∶ b ∷ a ∶ b :=
  proportion_iff.mpr ⟨a, b, 1, 1, ha, hb, (Nat.one_mul a).symm, (Nat.one_mul b).symm,
    (Nat.one_mul a).symm, (Nat.one_mul b).symm⟩

/-! Book 5 in Book 7.

Euclid cites Props. 5.7 and 5.9 in 7.19 and 5.13 in 7.33, and he uses 5.11 throughout,
of numbers. Proportion of numbers is Def. 7.20, not Def. 5.5, so these are not proved.
They are facts of the model: four numbers are proportional exactly when the product of the
outer is the product of the middle, by Mathlib's arithmetic. That is Prop. 7.19, proved
there in Euclid's way through these lemmas; the fact below is used only here. -/

/-- The model: `a ∶ b ∷ c ∶ d` exactly when `a * d = b * c`. From `a * d = b * c`, `a`,
`b` are `a`, `b` in least terms taken as many times as their greatest common measure, and
`c`, `d` the same terms taken some other number of times. -/
theorem proportion_iff_cross {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) :
    a ∶ b ∷ c ∶ d ↔ a * d = b * c := by
  rw [proportion_iff]
  constructor
  · rintro ⟨m, n, e, f, -, -, rfl, rfl, rfl, rfl⟩
    ring
  · intro h
    have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
    have hkl := Nat.coprime_div_gcd_div_gcd hg
    obtain ⟨k, hk⟩ := Nat.gcd_dvd_left a b
    obtain ⟨l, hl⟩ := Nat.gcd_dvd_right a b
    generalize Nat.gcd a b = g at hg hkl hk hl
    subst hk hl
    rw [Nat.mul_div_cancel_left _ hg, Nat.mul_div_cancel_left _ hg] at hkl
    have h' : k * d = l * c :=
      Nat.eq_of_mul_eq_mul_left hg (by simpa only [Nat.mul_assoc] using h)
    obtain ⟨t, rfl⟩ : k ∣ c := hkl.dvd_of_dvd_mul_left ⟨d, by rw [← h']⟩
    have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; omega)
    have hl0 : 0 < l := Nat.pos_of_ne_zero (by rintro rfl; omega)
    have hd : d = l * t := by
      apply Nat.eq_of_mul_eq_mul_left hk0
      rw [h']
      ring
    exact ⟨k, l, g, t, hk0, hl0, rfl, rfl, by ring, by rw [hd]; ring⟩

/-- Prop. 5.11 for numbers: ratios the same as the same ratio are the same as one
another. -- Missed by Euclid. -/
theorem proportion_trans {a b c d e f : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (h₁ : a ∶ b ∷ c ∶ d) (h₂ : c ∶ d ∷ e ∶ f) : a ∶ b ∷ e ∶ f := by
  rw [proportion_iff_cross ha hb] at h₁ ⊢
  rw [proportion_iff_cross hc hd] at h₂
  apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hc hd)
  calc c * d * (a * f) = (a * d) * (c * f) := by ring
    _ = (b * c) * (d * e) := by rw [h₁, h₂]
    _ = c * d * (b * e) := by ring

/-- Prop. 5.7 for numbers: equals have the same ratio to the same. -- Missed by
Euclid. -/
theorem proportion_of_eq {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (h : b = c) :
    a ∶ b ∷ a ∶ c :=
  h ▸ Proportion.refl ha hb

/-- Prop. 5.9 for numbers: those having the same ratio to the same are equal. -- Missed
by Euclid. -/
theorem eq_of_proportion {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a ∶ b ∷ a ∶ c) :
    b = c := by
  rw [proportion_iff_cross ha hb] at h
  exact Nat.eq_of_mul_eq_mul_left ha (h.trans (Nat.mul_comm b a)).symm

/-- Prop. 5.13 for numbers, as Euclid uses it in 7.33 (it is 5.14's step): if the first
is greater than the second, the third is greater than the fourth. -- Missed by Euclid. -/
theorem lt_of_proportion {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ∶ b ∷ c ∶ d) (hab : b < a) : d < c := by
  rw [proportion_iff_cross ha hb] at h
  by_contra hdc
  have : b * c < a * c := Nat.mul_lt_mul_of_pos_right hab hc
  have : a * d ≥ a * c := Nat.mul_le_mul_left a (by omega)
  omega

end Elements.Book7
