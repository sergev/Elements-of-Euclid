import Elements.Book10.Prop110

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- An apotome is not the same as a binomial. -/
theorem proposition_111 {l : Length} (ha : Apotome ρ l) : ¬ Binomial ρ l := by
  intro hb
  -- let the square on `l` be applied to the rational line `ρ`, making `g` as breadth: `g`
  -- is a first apotome [Prop. 10.97], `x` its whole and `y` attached, and a first
  -- binomial [Prop. 10.60], `x'` its greater term and `y'` the lesser
  obtain ⟨g, hg⟩ := Area.apply ρ (sq l)
  obtain ⟨x, y, ⟨⟨hx, hy, hxy, -⟩, -, hxρ⟩, hgx⟩ := proposition_97 ha (Rational.self ρ) hg
  obtain ⟨x', y', ⟨⟨-, hy', -, -⟩, -, hx'ρ⟩, rfl⟩ := proposition_60 hb
    (Rational.self ρ) hg
  -- `x` is commensurable with `x'` [Prop. 10.12], so with the remainder `w`, from the end
  -- of `x'` to that of `x` [Prop. 10.15]
  have hxx' : Commensurable x x' := proposition_12 Length.divisible hxρ hx'ρ
  have hw : x' + (y' + y) = x := by rw [← add_assoc]; exact hgx
  rw [← hw] at hxx'
  have hxw : Commensurable x (y' + y) := hw ▸ (proposition_15.1 (proposition_15.2 hxx')).2
  -- `w` is rational, and incommensurable with `y` [Prop. 10.13]: `w`, `y` are rational,
  -- commensurable in square only, and `y'`, their difference, is an apotome [Prop.
  -- 10.73]; but it is rational, which is impossible
  have hwr : Rational ρ (y' + y) := hx.of_comm hxw.symm
  have hwy : ¬ Commensurable (y' + y) y := proposition_13 Length.divisible hxw hxy.2
  exact proposition_73 hwr hy ⟨hwr.inSquare_of hy, hwy⟩ rfl hy'

/-! The thirteen irrational lines, and the corollary to 10.111. -/

/-- The orders of Defs. II and III, first to sixth (`0` to `5`): the conditions on the
terms (`FirstTerms`, …, `SixthTerms`). -/
def OrderTerms (ρ r : Length) : Fin 6 → Length → Length → Prop
  | ⟨0, _⟩ => FirstTerms ρ r
  | ⟨1, _⟩ => SecondTerms ρ r
  | ⟨2, _⟩ => ThirdTerms ρ r
  | ⟨3, _⟩ => FourthTerms ρ r
  | ⟨4, _⟩ => FifthTerms ρ r
  | ⟨5, _⟩ => SixthTerms ρ r

/-- What an order says: the square on the greater term exceeds that on the lesser by the
square on a line commensurable with it (the first three) or incommensurable (the last
three); and the greater term is commensurable with `r` (first and fourth), or the lesser
(second and fifth), or neither. -/
theorem OrderTerms.data {r x y : Length} {k : Fin 6} (h : OrderTerms ρ r k x y) :
    BinomialTerms ρ x y ∧ (k.val < 3 → ExceedsComm x y) ∧
      (3 ≤ k.val → ExceedsIncomm x y) ∧
      (k.val % 3 = 0 → Commensurable x r) ∧ (k.val % 3 = 1 → Commensurable y r) ∧
      (k.val % 3 = 2 → ¬ Commensurable x r ∧ ¬ Commensurable y r) := by
  match k, h with
  | ⟨0, _⟩, ⟨h₁, h₂, h₃⟩ =>
    exact ⟨h₁, fun _ => h₂, by simp, fun _ => h₃, by simp, by simp⟩
  | ⟨1, _⟩, ⟨h₁, h₂, h₃⟩ =>
    exact ⟨h₁, fun _ => h₂, by simp, by simp, fun _ => h₃, by simp⟩
  | ⟨2, _⟩, ⟨h₁, h₂, h₃⟩ =>
    exact ⟨h₁, fun _ => h₂, by simp, by simp, by simp, fun _ => h₃⟩
  | ⟨3, _⟩, ⟨h₁, h₂, h₃⟩ =>
    exact ⟨h₁, by simp, fun _ => h₂, fun _ => h₃, by simp, by simp⟩
  | ⟨4, _⟩, ⟨h₁, h₂, h₃⟩ =>
    exact ⟨h₁, by simp, fun _ => h₂, by simp, fun _ => h₃, by simp⟩
  | ⟨5, _⟩, ⟨h₁, h₂, h₃⟩ =>
    exact ⟨h₁, by simp, fun _ => h₂, by simp, by simp, fun _ => h₃⟩

/-- The square on the greater term does not exceed that on the lesser both by the square
on a line commensurable with it and by one incommensurable: it is the same line. -/
theorem not_exceeds_both {x y : Length} (h : ExceedsComm x y) (h' : ExceedsIncomm x y) :
    False := by
  obtain ⟨z, hz, hzx⟩ := h
  obtain ⟨z', hz', hz'x⟩ := h'
  exact hz'x (sq_inj (add_left_cancel (hz'.trans hz.symm)) ▸ hzx)

/-- A binomial or an apotome has one order only: the terms are of one order only. -/
theorem OrderTerms.unique {r x y : Length} {i j : Fin 6} (hi : OrderTerms ρ r i x y)
    (hj : OrderTerms ρ r j x y) : i = j := by
  obtain ⟨⟨-, -, hxy, -⟩, hci, hii, hi₀, hi₁, hi₂⟩ := hi.data
  obtain ⟨-, hcj, hij, hj₀, hj₁, hj₂⟩ := hj.data
  -- of the same excess
  have h₁ : (i.val < 3 ↔ j.val < 3) := by
    constructor <;> intro h <;> by_contra h' <;> push Not at h'
    · exact not_exceeds_both (hci h) (hij h')
    · exact not_exceeds_both (hcj h) (hii h')
  -- and the same term commensurable with `r`: not both, the terms being incommensurable
  -- [Prop. 10.12]
  have both : Commensurable x r → Commensurable y r → False :=
    fun hx hy => hxy.2 (proposition_12 Length.divisible hx hy)
  have h₂ : i.val % 3 = j.val % 3 := by
    have : i.val % 3 < 3 := Nat.mod_lt _ (by decide)
    have : j.val % 3 < 3 := Nat.mod_lt _ (by decide)
    rcases (by omega : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2) with
      ha | ha | ha <;>
    rcases (by omega : j.val % 3 = 0 ∨ j.val % 3 = 1 ∨ j.val % 3 = 2) with
      hb | hb | hb <;>
    first
    | omega
    | exact (both (hi₀ ha) (hj₁ hb)).elim
    | exact (both (hj₀ hb) (hi₁ ha)).elim
    | exact ((hj₂ hb).1 (hi₀ ha)).elim
    | exact ((hj₂ hb).2 (hi₁ ha)).elim
    | exact ((hi₂ ha).1 (hj₀ hb)).elim
    | exact ((hi₂ ha).2 (hj₁ hb)).elim
  apply Fin.ext
  have := i.isLt; have := j.isLt
  by_cases h : i.val < 3 <;> omega

/-- The terms of the six irrational sums and differences, in Euclid's order: binomial,
first and second bimedial, major, square root of a rational plus a medial area, of two
medial areas. -/
def SumTerms (ρ : Length) : Fin 6 → Length → Length → Prop
  | ⟨0, _⟩ => BinomialTerms ρ
  | ⟨1, _⟩ => FirstBimedialTerms ρ
  | ⟨2, _⟩ => SecondBimedialTerms ρ
  | ⟨3, _⟩ => MajorTerms ρ
  | ⟨4, _⟩ => RationalMedialTerms ρ
  | ⟨5, _⟩ => TwoMedialTerms ρ

/--
The thirteen irrational lines, in Euclid's order: the medial; the six sums (binomial,
first bimedial, second bimedial, major, square root of a rational plus a medial area, of
two medial areas); the six differences (apotome, first and second apotome of a medial,
minor, that which with a rational area makes a medial whole, that which with a medial area
makes a medial whole).
-/
inductive LineKind
  | medial
  | sum (k : Fin 6)
  | diff (k : Fin 6)

/-- A line of the kind: `sum k` with the terms of `SumTerms ρ k` added, `diff k` with the
lesser taken from the greater (`Binomial`, …, `MedialWholeWithMedial`). -/
def LineKind.Is (ρ : Length) : LineKind → Length → Prop
  | medial => Medial ρ
  | sum k => fun l => ∃ x y, SumTerms ρ k x y ∧ l = x + y
  | diff k => fun l => ∃ x y, SumTerms ρ k x y ∧ l + y = x

/-- The breadth the square on a line of the kind makes, applied to the rational line `ρ`:
rational and incommensurable with `ρ` (10.22), a binomial of the order (10.60–10.65), an
apotome of the order (10.97–10.102). -/
def LineKind.Breadth (ρ : Length) : LineKind → Length → Prop
  | medial => fun g => Rational ρ g ∧ ¬ Commensurable g ρ
  | sum k => fun g => ∃ x y, OrderTerms ρ ρ k x y ∧ g = x + y
  | diff k => fun g => ∃ x y, OrderTerms ρ ρ k x y ∧ g + y = x

theorem LineKind.breadth {k : LineKind} {l g : Length} (h : k.Is ρ l)
    (hg : rect ρ g = sq l) : k.Breadth ρ g := by
  have hr := Rational.self ρ
  match k with
  | .medial => exact proposition_22 h hr hg
  | .sum ⟨0, _⟩ => exact proposition_60 h hr hg
  | .sum ⟨1, _⟩ => exact proposition_61 h hr hg
  | .sum ⟨2, _⟩ => exact proposition_62 h hr hg
  | .sum ⟨3, _⟩ => exact proposition_63 h hr hg
  | .sum ⟨4, _⟩ => exact proposition_64 h hr hg
  | .sum ⟨5, _⟩ => exact proposition_65 h hr hg
  | .diff ⟨0, _⟩ => exact proposition_97 h hr hg
  | .diff ⟨1, _⟩ => exact proposition_98 h hr hg
  | .diff ⟨2, _⟩ => exact proposition_99 h hr hg
  | .diff ⟨3, _⟩ => exact proposition_100 h hr hg
  | .diff ⟨4, _⟩ => exact proposition_101 h hr hg
  | .diff ⟨5, _⟩ => exact proposition_102 h hr hg

/-- The breadths differ: the first is rational, and a binomial or an apotome is not
[Props. 10.36, 10.73]; binomials, or apotomes, of different orders are different, a
binomial being divided at one point only and an apotome having one line attached [Props.
10.42, 10.79]; and a binomial is not an apotome [Prop. 10.111]. -/
theorem LineKind.breadth_unique {k k' : LineKind} {g : Length} (h : k.Breadth ρ g)
    (h' : k'.Breadth ρ g) : k = k' := by
  have sum_irr : ∀ {k g}, (LineKind.sum k).Breadth ρ g → ¬ Rational ρ g := by
    rintro k g ⟨x, y, hk, rfl⟩
    obtain ⟨hx, hy, hxy, -⟩ := hk.data.1
    exact proposition_36 hx hy hxy
  have diff_irr : ∀ {k g}, (LineKind.diff k).Breadth ρ g → ¬ Rational ρ g := by
    rintro k g ⟨x, y, hk, hl⟩
    obtain ⟨hx, hy, hxy, -⟩ := hk.data.1
    exact proposition_73 hx hy hxy hl
  match k, k' with
  | .medial, .medial => rfl
  | .medial, .sum _ => exact absurd h.1 (sum_irr h')
  | .medial, .diff _ => exact absurd h.1 (diff_irr h')
  | .sum _, .medial => exact absurd h'.1 (sum_irr h)
  | .diff _, .medial => exact absurd h'.1 (diff_irr h)
  | .sum i, .sum j =>
    obtain ⟨x, y, hi, rfl⟩ := h
    obtain ⟨x', y', hj, he⟩ := h'
    obtain ⟨rfl, rfl⟩ := proposition_42 hi.data.1 hj.data.1 he
    rw [hi.unique hj]
  | .diff i, .diff j =>
    obtain ⟨x, y, hi, hl⟩ := h
    obtain ⟨x', y', hj, hl'⟩ := h'
    obtain ⟨rfl, rfl⟩ := proposition_79 hi.data.1 hj.data.1 hl hl'
    rw [hi.unique hj]
  | .sum _, .diff _ =>
    obtain ⟨x, y, hi, rfl⟩ := h
    obtain ⟨x', y', hj, hl⟩ := h'
    exact absurd ⟨x, y, hi.data.1, rfl⟩ (proposition_111 ⟨x', y', hj.data.1, hl⟩)
  | .diff _, .sum _ =>
    obtain ⟨x, y, hi, hl⟩ := h
    obtain ⟨x', y', hj, rfl⟩ := h'
    exact absurd ⟨x', y', hj.data.1, rfl⟩ (proposition_111 ⟨x, y, hi.data.1, hl⟩)

/--
10.111, corollary: the thirteen irrational lines are different from one another: no line
is of two of the kinds. As Euclid argues, the square on a line of each kind, applied to a
rational line, makes a breadth of a kind of its own, and the breadths differ. What is
proved is that the kinds exclude one another, for any assigned `ρ`; not that each kind has
lines (that is 10.21's, 10.27–10.35's and 10.48–10.53's business).
-/
theorem proposition_111_corollary {k k' : LineKind} {l : Length} (h : k.Is ρ l)
    (h' : k'.Is ρ l) : k = k' := by
  obtain ⟨g, hg⟩ := Area.apply ρ (sq l)
  exact LineKind.breadth_unique (LineKind.breadth h hg) (LineKind.breadth h' hg)

end Elements.Book10
