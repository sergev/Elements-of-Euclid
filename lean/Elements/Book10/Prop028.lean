import Elements.Book9
import Elements.Book10.Prop027

namespace Elements.Book10

open Elements.Book5 Elements.Book7 Number

variable {ρ : Length}

/-- A number between the squares on `k` and `k + 1` is not square: the side would fall
between `k` and `k + 1`, and the unit would be divided. -/
theorem not_square_of_between {a k : ℕ} (h₁ : k * k < a) (h₂ : a < (k + 1) * (k + 1)) :
    ¬ SquareNumber a := by
  rintro ⟨p, -, rfl⟩
  rcases Nat.lt_or_ge k p with h | h
  · exact absurd (Nat.mul_le_mul h h) (not_le.mpr h₂)
  · exact absurd (Nat.mul_le_mul h h) (not_le.mpr h₁)

/-- Numbers `a`, `b`, one square and the other not, do not have the ratio of a square
number to a square number [Prop. 8.24]. -/
theorem not_square_ratio_of {a b : ℕ+}
    (h : (SquareNumber a ∧ 1 < (b : ℕ) ∧ ¬ SquareNumber b) ∨
    (SquareNumber b ∧ 1 < (a : ℕ) ∧ ¬ SquareNumber a)) :
    ¬ ∃ c d : ℕ+, Proportion (a : Number) (b : Number) ((c : Number) * c)
      ((d : Number) * d) := by
  rintro ⟨c, d, h'⟩
  have h'' := number_proportion_iff.mp h'
  simp only [val_coe, val_mul] at h''
  rcases h with ⟨ha, hb, hnb⟩ | ⟨hb, ha, hna⟩
  · exact hnb (Elements.Book8.proposition_24 c.pos d.pos hb h'' ha)
  · exact hna (Elements.Book8.proposition_24 d.pos c.pos ha h''.inv hb)

/-- Numbers are proportional when the product of the outer is the product of the middle,
checked by multiplying. -/
theorem number_proportion {a b c d : ℕ+} (h : (a : ℕ) * d = b * c) :
    Proportion (a : Number) (b : Number) (c : Number) (d : Number) :=
  proportion_iff_mul.mpr (by
    show ((a : ℕ) : ℝ) * (d : ℕ) = (b : ℕ) * (c : ℕ)
    exact_mod_cast h)

/-- Lines whose squares are as two numbers not as a square number to a square number are
commensurable in square only [Props. 10.6, 10.9]. -/
theorem inSquareOnly_of_ratio {a b : Length} {m n : ℕ+}
    (h : Proportion (m : Number) (n : Number) (sq a) (sq b))
    (hns : ¬ ∃ c d : ℕ+, Proportion (m : Number) (n : Number) ((c : Number) * c)
      ((d : Number) * d)) : InSquareOnly a b :=
  ⟨proposition_6 h.symm (Area.divisible _ _), fun hc => hns (by
    obtain ⟨c, d, h'⟩ := proposition_9.mp hc
    exact ⟨c, d, Elements.Book5.proposition_11 h h'⟩)⟩

/-- Three rational lines commensurable in square only, `ρ` and two others: their squares
as `16`, `12`, `6` [Prop. 10.6 corr.]. Euclid lays them down without saying how. -/
theorem exists_three_inSquareOnly (ρ : Length) :
    ∃ b c, Rational ρ b ∧ Rational ρ c ∧ InSquareOnly ρ b ∧ InSquareOnly b c ∧
      InSquareOnly ρ c := by
  obtain ⟨-, b, -, hb⟩ := proposition_6_corollary 4 3 ρ
  obtain ⟨-, c, -, hc⟩ := proposition_6_corollary 4 2 b
  have sq4 : SquareNumber ((4 : ℕ+) : ℕ) := ⟨2, by decide, rfl⟩
  have sq16 : SquareNumber ((16 : ℕ+) : ℕ) := ⟨4, by decide, rfl⟩
  have hab := inSquareOnly_of_ratio hb (not_square_ratio_of (Or.inl ⟨sq4, by decide,
    not_square_of_between (k := 1) (by decide) (by decide)⟩))
  have hbc := inSquareOnly_of_ratio hc (not_square_ratio_of (Or.inl ⟨sq4, by decide,
    not_square_of_between (k := 1) (by decide) (by decide)⟩))
  -- as `16` to `12`, so `4` to `3`, and as `12` to `6`, so `4` to `2`: via equality
  -- [Prop. 5.22]
  have h₁ : Proportion ((16 : ℕ+) : Number) ((12 : ℕ+) : Number) (sq ρ) (sq b) :=
    Elements.Book5.proposition_11 (number_proportion (by decide)) hb
  have h₂ : Proportion ((12 : ℕ+) : Number) ((6 : ℕ+) : Number) (sq b) (sq c) :=
    Elements.Book5.proposition_11 (number_proportion (by decide)) hc
  have hac := inSquareOnly_of_ratio (Elements.Book5.proposition_22' h₁ h₂)
    (not_square_ratio_of (Or.inl ⟨sq16, by decide,
      not_square_of_between (k := 2) (by decide) (by decide)⟩))
  have hbr : Rational ρ b := Rational.of_inSquare (Rational.self ρ) hab.1.symm
  exact ⟨b, c, hbr, Rational.of_inSquare hbr hbc.1.symm, hab, hbc, hac⟩

/-- To find two medial lines commensurable in square only, containing a medial area. -/
theorem proposition_28 :
    ∃ d e, Medial ρ d ∧ Medial ρ e ∧ InSquareOnly d e ∧ MedialArea ρ (rect d e) := by
  -- let the rational lines `a`, `b`, `c`, commensurable in square only, be laid down
  obtain ⟨b, c, hb, hc, hab, hbc, hac⟩ := exists_three_inSquareOnly ρ
  have ha := Rational.self ρ
  -- the mean proportional `d` of `a`, `b` [Prop. 6.13], and `e` with `b ∶ c ∷ d ∶ e`
  -- [Prop. 6.12]
  obtain ⟨d, hd⟩ := Length.mean ρ b
  obtain ⟨e, he⟩ := Length.fourth' b c d
  -- the rectangle contained by `a`, `b`, the square on `d` [Prop. 6.17], is medial, and
  -- `d` is medial [Prop. 10.21]
  have hdm : Medial ρ d := ⟨ρ, b, ha, hb, hab, (rect_eq_sq_of_proportion hd).symm⟩
  -- `d`, `e` are commensurable in square only [Prop. 10.11]; `e` is medial [Prop. 10.23]
  have hde := hbc.of_proportion he
  have hem := proposition_23 hdm hde.1.symm
  -- alternately, as `b` is to `d`, so `c` to `e` [Prop. 5.16]; and as `b` to `d`, so `d`
  -- to `a`: so as `d` to `a`, so `c` to `e` [Prop. 5.11], and the rectangle contained by
  -- `a`, `c` is that contained by `d`, `e` [Prop. 6.16], medial [Prop. 10.21]
  have h₁ : Proportion d ρ c e := Elements.Book5.proposition_11
    (Elements.Book5.proposition_7_corollary hd) (Elements.Book5.proposition_16 he)
  exact ⟨d, e, hdm, hem, hde, ⟨ρ, c, ha, hc, hac, rect_eq_of_proportion h₁⟩⟩

/--
10.28, Lemma I: to find two square numbers whose sum is square. Let `a`, `b` be both even
or both odd, so that their difference is even, `d + d` [Props. 9.24, 9.26]. The number
made by `a` and `b`, with the square on `d`, is the square on `b + d` [Prop. 2.6]; and if
`a`, `b` are similar plane numbers, or squares, the number made by them is square [Prop.
9.1]. And if they are not similar plane numbers, the difference of the squares on `b + d`
and `d`, the number made by `a`, `b`, is not square [Prop. 9.2].
-/
theorem proposition_28_lemma_1 {a b d : ℕ} (ha : a = b + d + d) :
    a * b + d * d = (b + d) * (b + d) ∧
    (∀ p q r s, 0 < p → 0 < q → 0 < r → 0 < s → 1 < p * q → a = p * q → b = r * s →
      p ∶ q ∷ r ∶ s → SquareNumber (a * b)) ∧
    (0 < a → 0 < b → (¬ ∃ p q r s, 0 < p ∧ 0 < q ∧ 0 < r ∧ 0 < s ∧ a = p * q ∧ b = r * s ∧
      p ∶ q ∷ r ∶ s) → ¬ SquareNumber (a * b)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- [Prop. 2.6], for numbers; commutativity is Prop. 7.16
    subst ha; ring
  · intro p q r s hp hq hr hs hpq hap hbr h
    have := Elements.Book9.proposition_1 hp hq hr hs hpq h
    rwa [← hap, ← hbr, Nat.mul_comm] at this
  · rintro ha0 hb0 hns ⟨x, hx, hab⟩
    exact hns (Elements.Book9.proposition_2 ha0 hb0 (by omega)
      ((Nat.mul_comm b a).trans hab))

/--
10.28, Lemma II: to find two square numbers whose sum is not square. Let the number made
by `a` and `b` be square, `a = b + d + d`, and take the unit from `d`: the number made by
`a`, `b`, with the square on `d - 1`, is not square. Its side would be greater than
`b + d - 1`, or equal, or less. Not greater, for it is less than the square on `b + d`
[Lemma I], and the unit would be divided; not equal, for then, with `a - 2` and `b`, the
square on `b + d - 1` is two numbers [Prop. 2.6], and `a - 2` would be `a`; and not less.
-/
theorem proposition_28_lemma_2 {a b d : ℕ} (ha : a = b + d + d) (hb : 0 < b) (hd : 1 < d)
    (_hsq : SquareNumber (a * b)) : ¬ SquareNumber (a * b + (d - 1) * (d - 1)) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  subst ha
  simp only [Nat.add_sub_cancel]
  -- not greater than `b + e` (the unit would be divided), not equal, not less: it falls
  -- between the squares on `b + e` and `b + e + 1`. The last is missed by Euclid.
  exact not_square_of_between (k := b + e) (by nlinarith) (by nlinarith)

end Elements.Book10
