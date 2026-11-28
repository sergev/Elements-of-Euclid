import Elements.Book5
import Elements.Book7.Lemmas
import Elements.Book10.Definitions3

/-
The commensurability of Book 5's magnitudes, as Euclid takes it for granted, and the
facts of the model: lengths, areas and numbers measured by positive reals, the facts of
Books 2 and 6 about squares and rectangles that Book 10 cites, and the constructions by
which Euclid finds lines.
-/

namespace Elements.Book10

open Elements.Book5 Elements.Book5.Magnitude

variable {M : Type*} [Magnitude M]

/-! Measures and commensurable magnitudes. -/

theorem Measures.refl (a : M) : Measures a a := ⟨1, rfl⟩

/-- What measures a measure measures the magnitude (5.3). -/
theorem Measures.trans {a b c : M} (h₁ : Measures a b) (h₂ : Measures b c) :
    Measures a c := by
  obtain ⟨m, rfl⟩ := h₁
  obtain ⟨n, rfl⟩ := h₂
  exact ⟨n * m, Elements.Book5.proposition_3 m n a⟩

/-- A measure of two magnitudes measures their sum (5.2). -/
theorem Measures.add {a b c : M} (h₁ : Measures a b) (h₂ : Measures a c) :
    Measures a (b + c) := by
  obtain ⟨m, rfl⟩ := h₁
  obtain ⟨n, rfl⟩ := h₂
  exact ⟨m + n, Elements.Book5.proposition_2 m n a⟩

theorem Measures.mult {a b : M} (h : Measures a b) (n : ℕ+) : Measures a (n • b) :=
  h.trans ⟨n, rfl⟩

/-- A measure of the whole and of a part measures the remainder (5.5). -/
theorem Measures.sub {a b c : M} (h₁ : Measures a (b + c)) (h₂ : Measures a b) :
    Measures a c := by
  obtain ⟨m, hm⟩ := h₁
  obtain ⟨n, rfl⟩ := h₂
  have hlt : n < m := lt_of_mult_lt_mult_left (hm ▸ lt_add (n • a) c)
  obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, (PNat.add_sub_of_lt hlt).symm⟩
  refine ⟨k, add_left_cancel (a := n • a) ?_⟩
  rw [hm, Elements.Book5.proposition_2]

/-- The measure is not greater than what it measures. -/
theorem Measures.le {a b : M} (h : Measures a b) : a ≤ b := by
  obtain ⟨n, rfl⟩ := h
  exact mult_le_mult_left a (PNat.coe_le_coe 1 n |>.mp n.pos)

theorem Commensurable.refl (a : M) : Commensurable a a := ⟨a, .refl a, .refl a⟩

theorem Commensurable.symm {a b : M} (h : Commensurable a b) : Commensurable b a :=
  let ⟨c, h₁, h₂⟩ := h; ⟨c, h₂, h₁⟩

theorem Commensurable.of_measures {a b : M} (h : Measures a b) : Commensurable a b :=
  ⟨a, .refl a, h⟩

theorem not_commensurable_symm {a b : M} (h : ¬ Commensurable a b) :
    ¬ Commensurable b a := fun h' => h h'.symm

theorem Rational.self (ρ : Length) : Rational ρ ρ := Or.inl (.refl ρ)

/-! The model. -/

/--
The magnitudes of the model, lengths, areas and numbers, each measured by a positive real
`val`, with multiples, order and equality as of reals. Used only in this file.
-/
class Model (K : Type) [Magnitude K] where
  val : K → ℝ
  pos : ∀ a, 0 < val a
  val_mult : ∀ (n : ℕ+) (a : K), val (n • a) = n * val a
  val_lt : ∀ {a b : K}, val a < val b ↔ a < b
  val_inj : ∀ {a b : K}, val a = val b ↔ a = b
  val_add : ∀ a b : K, val (a + b) = val a + val b

noncomputable instance : Model Length where
  val a := a.1
  pos a := a.2
  val_mult := Positive.mult_val
  val_lt := Iff.rfl
  val_inj := Subtype.ext_iff.symm
  val_add := Positive.coe_add

noncomputable instance : Model Area where
  val a := a.1
  pos a := a.2
  val_mult := Positive.mult_val
  val_lt := Iff.rfl
  val_inj := Subtype.ext_iff.symm
  val_add := Positive.coe_add

instance : Model Number where
  val a := (a.val : ℝ)
  pos a := by exact_mod_cast a.val_pos
  val_mult n a := by rw [Number.mult_val]; push_cast; rfl
  val_lt := by intro a b; rw [Nat.cast_lt]; exact Number.val_lt
  val_inj := by intro a b; rw [Nat.cast_inj]; exact Number.val_inj
  val_add a b := by rw [Number.val_add]; push_cast; rfl

open Model in
/-- The model: `p ∶ q ∷ r ∶ s` (Def. 5.5) exactly when `p * s = q * r`. Between two
unequal ratios of reals falls a ratio of numbers. -/
theorem proportion_iff_mul {K L : Type} [Magnitude K] [Magnitude L] [Model K] [Model L]
    {p q : K} {r s : L} : Proportion p q r s ↔ val p * val s = val q * val r := by
  have hp := pos p
  have hq := pos q
  have hr := pos r
  have hs := pos s
  have lt_iff : ∀ {K} [Magnitude K] [Model K] {a b : K} (m n : ℕ+),
      m • a < n • b ↔ (m : ℝ) * val a < n * val b := by
    intro K _ _ a b m n; rw [← val_mult, ← val_mult, val_lt]
  have eq_iff : ∀ {K} [Magnitude K] [Model K] {a b : K} (m n : ℕ+),
      m • a = n • b ↔ (m : ℝ) * val a = n * val b := by
    intro K _ _ a b m n; rw [← val_mult, ← val_mult, val_inj]
  -- between two unequal ratios, a ratio `n / m` of numbers
  have btwn : ∀ {x y : ℝ}, 0 < x → x < y →
      ∃ m n : ℕ+, (m : ℝ) * x < n ∧ (n : ℝ) < m * y := by
    intro x y hx hxy
    obtain ⟨t, ht₁, ht₂⟩ := exists_rat_btwn hxy
    have ht : 0 < t := by exact_mod_cast hx.trans ht₁
    have hnum : 0 < t.num := Rat.num_pos.mpr ht
    have hd : (0 : ℝ) < t.den := by exact_mod_cast t.den_pos
    have ht' : (t : ℝ) = t.num / t.den := by exact_mod_cast (Rat.num_div_den t).symm
    have hn : ((t.num.toNat : ℕ) : ℝ) = t.num := by
      exact_mod_cast Int.toNat_of_nonneg hnum.le
    rw [ht', lt_div_iff₀ hd] at ht₁
    rw [ht', div_lt_iff₀ hd] at ht₂
    refine ⟨⟨t.den, t.den_pos⟩, ⟨t.num.toNat, by omega⟩, ?_, ?_⟩ <;>
      simp only [PNat.mk_coe, hn] <;> linarith
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · -- `p / q < r / s`
      obtain ⟨m, n, h₁, h₂⟩ := btwn (x := val p / val q) (y := val r / val s)
        (div_pos hp hq) (by rw [div_lt_div_iff₀ hq hs]; linarith)
      rw [mul_div_assoc', div_lt_iff₀ hq] at h₁
      rw [mul_div_assoc', lt_div_iff₀ hs] at h₂
      have := ((h.lt m n).mp ((lt_iff m n).mpr (by linarith)))
      rw [lt_iff] at this
      linarith
    · obtain ⟨m, n, h₁, h₂⟩ := btwn (x := val r / val s) (y := val p / val q)
        (div_pos hr hs) (by rw [div_lt_div_iff₀ hs hq]; linarith)
      rw [mul_div_assoc', div_lt_iff₀ hs] at h₁
      rw [mul_div_assoc', lt_div_iff₀ hq] at h₂
      have := ((h.lt m n).mpr ((lt_iff m n).mpr (by linarith)))
      rw [lt_iff] at this
      linarith
  · intro h
    refine ⟨fun m n => ?_, fun m n => ?_, fun m n => ?_⟩
    · rw [lt_iff, lt_iff]
      have hm : (0 : ℝ) < m := by exact_mod_cast m.pos
      have hn : (0 : ℝ) < n := by exact_mod_cast n.pos
      constructor <;> intro h' <;> nlinarith
    · rw [eq_iff, eq_iff]
      have hm : (0 : ℝ) < m := by exact_mod_cast m.pos
      constructor <;> intro h'
      · apply mul_right_cancel₀ (ne_of_gt hq)
        linear_combination val s * h' - (m : ℝ) * h
      · apply mul_right_cancel₀ (ne_of_gt hs)
        linear_combination val q * h' + (m : ℝ) * h
    · rw [lt_iff, lt_iff]
      have hm : (0 : ℝ) < m := by exact_mod_cast m.pos
      have hn : (0 : ℝ) < n := by exact_mod_cast n.pos
      constructor <;> intro h' <;> nlinarith

/-! Numbers: Book 5's proportion and Book 7's. -/

/--
Four numbers are proportional by Def. 5.5 exactly when they are by Def. 7.20: both say
that the product of the outer is the product of the middle (`proportion_iff_mul`, Book 7's
`proportion_iff_cross`). Euclid passes from one to the other without comment in 10.5–10.9.
-- Missed by Euclid.
-/
theorem number_proportion_iff {a b c d : Number} :
    Proportion a b c d ↔ Elements.Book7.Proportion a.val b.val c.val d.val := by
  rw [proportion_iff_mul, Elements.Book7.proportion_iff_cross a.val_pos b.val_pos]
  show (a.val : ℝ) * d.val = b.val * c.val ↔ _
  exact_mod_cast Iff.rfl

/-! Lines and areas in the model. -/

open Model

/-- The line of length `x`. -/
def Length.mk' (x : ℝ) (h : 0 < x) : Length := ⟨x, h⟩

/-- The area of size `x`. -/
def Area.mk' (x : ℝ) (h : 0 < x) : Area := ⟨x, h⟩

@[simp] theorem val_length_mk (x : ℝ) (h : 0 < x) : val (Length.mk' x h) = x := rfl

@[simp] theorem val_area_mk (x : ℝ) (h : 0 < x) : val (Area.mk' x h) = x := rfl

@[simp] theorem val_sq (a : Length) : val (sq a) = val a * val a := rfl

@[simp] theorem val_rect (a b : Length) : val (rect a b) = val a * val b := rfl

attribute [simp] Model.val_add Model.val_mult

theorem Model.ext {K : Type} [Magnitude K] [Model K] {a b : K} (h : val a = val b) :
    a = b := val_inj.mp h

/-- A positive real has a square root: the least upper bound of the reals whose squares
do not exceed it. A fact of the model, for Props. 2.14 and 6.13. -/
theorem exists_mul_self {A : ℝ} (hA : 0 < A) : ∃ x : ℝ, 0 < x ∧ x * x = A := by
  set S := {x : ℝ | 0 ≤ x ∧ x * x ≤ A}
  have hbdd : BddAbove S := ⟨A + 1, fun x ⟨hx, hxA⟩ => by nlinarith⟩
  have ht : min 1 A ∈ S := ⟨by positivity, by
    have h1 := min_le_left 1 A; have h2 := min_le_right 1 A
    have h0 : 0 < min 1 A := lt_min one_pos hA
    nlinarith⟩
  set s := sSup S
  have hs : min 1 A ≤ s := le_csSup hbdd ht
  have hs0 : 0 < s := lt_of_lt_of_le (lt_min one_pos hA) hs
  refine ⟨s, hs0, ?_⟩
  rcases lt_trichotomy (s * s) A with h | h | h
  · exfalso
    set ε := min s ((A - s * s) / (3 * s))
    have hε : 0 < ε := lt_min hs0 (div_pos (by linarith) (by linarith))
    have hε1 : ε ≤ s := min_le_left _ _
    have hε2 : ε * (3 * s) ≤ A - s * s := by
      have := min_le_right s ((A - s * s) / (3 * s))
      rwa [le_div_iff₀ (by linarith)] at this
    have : s + ε ∈ S := ⟨by linarith, by nlinarith⟩
    have := le_csSup hbdd this
    linarith
  · exact h
  · exfalso
    set ε := (s * s - A) / (2 * s)
    have hε : 0 < ε := div_pos (by linarith) (by linarith)
    have hε2 : ε * (2 * s) = s * s - A := div_mul_cancel₀ _ (by positivity)
    have hε1 : ε < s := by nlinarith
    have : s ≤ s - ε := csSup_le ⟨_, ht⟩ fun x ⟨hx, hxA⟩ => by
      by_contra hc; nlinarith [not_le.mp hc]
    linarith

/-! Books 2 and 6 on squares and rectangles, proved in the model. Book 2's and Book 6's
propositions are about points of System E, and a `Length` is not a segment of the plane;
so Book 10 has these as lemmas, each naming the proposition it stands for. -/

/-- The rectangle contained by `a` and `b` is the rectangle contained by `b` and `a`. -/
theorem rect_comm (a b : Length) : rect a b = rect b a := Model.ext (by simp [mul_comm])

theorem sq_eq_rect (a : Length) : sq a = rect a a := rfl

/-- Prop. 6.1: rectangles of the same height are to one another as their bases. -/
theorem rect_proportion (a b c : Length) : Proportion (rect a c) (rect b c) a b :=
  proportion_iff_mul.mpr (by simp; ring)

/-- Prop. 6.1, the height first. -/
theorem rect_proportion' (a b c : Length) : Proportion (rect c a) (rect c b) a b :=
  proportion_iff_mul.mpr (by simp; ring)

/-- Prop. 6.22: if four lines are proportional, the squares on them are proportional;
and conversely. -/
theorem proportion_sq {a b c d : Length} :
    Proportion a b c d ↔ Proportion (sq a) (sq b) (sq c) (sq d) := by
  rw [proportion_iff_mul, proportion_iff_mul]
  simp only [val_sq]
  have := pos a; have := pos b; have := pos c; have := pos d
  constructor
  · intro h; calc _ = (val a * val d) * (val a * val d) := by ring
      _ = _ := by rw [h]; ring
  · intro h
    have h' : (val a * val d) * (val a * val d) = (val b * val c) * (val b * val c) := by
      linear_combination h
    rcases mul_self_eq_mul_self_iff.mp h' with h'' | h''
    · exact h''
    · nlinarith [mul_pos ‹0 < val a› ‹0 < val d›, mul_pos ‹0 < val b› ‹0 < val c›]

/-- Prop. 6.20 (its corollary): the square on `a` has to the square on `b` the squared
ratio of `a` to `b` (Def. 5.9): as `a` to the third proportional `e`. -/
theorem squaredRatio_sq (a b : Length) : SquaredRatio (sq a) (sq b) a b := by
  have ha := pos a
  refine ⟨Length.mk' (val b * val b / val a) (div_pos (mul_pos (pos b) (pos b)) ha),
    ?_, ?_⟩
    <;> refine proportion_iff_mul.mpr ?_ <;> simp <;> field_simp

/-- Prop. 2.1, for a line cut once: the rectangle contained by `a` and `b + c` is the
rectangles contained by `a`, `b` and by `a`, `c`. -/
theorem rect_add (a b c : Length) : rect a (b + c) = rect a b + rect a c :=
  Model.ext (by simp; ring)

/-- Prop. 2.4: the square on `a + b` is the squares on `a` and `b` and twice the
rectangle contained by them. -/
theorem sq_add (a b : Length) : sq (a + b) = sq a + sq b + (2 : ℕ+) • rect a b :=
  Model.ext (by simp; ring)

/-- Prop. 2.7: if `x` is cut into `l` and `y`, the squares on `x` and `y` are twice the
rectangle contained by `x`, `y` and the square on `l`. -/
theorem sq_add_sq_of_sub {l x y : Length} (h : l + y = x) :
    sq x + sq y = (2 : ℕ+) • rect x y + sq l := by
  subst h; exact Model.ext (by simp; ring)

/-! The constructions by which Euclid finds lines, in the model. -/

/-- Prop. 6.9: to cut off a prescribed part from a line, the `n`th part. -/
theorem Length.part (a : Length) (n : ℕ+) : ∃ c : Length, a = n • c := by
  have hn : (0 : ℝ) < n := by exact_mod_cast n.pos
  exact ⟨Length.mk' (val a / n) (div_pos (pos a) hn), Model.ext (by simp; field_simp)⟩

/-- Prop. 6.12: to find a fourth proportional to two magnitudes and a line: as `p` to
`q`, so `c` to some line. For areas `p`, `q` Euclid applies them to a line first (6.1). -/
theorem Length.fourth' {K : Type} [Magnitude K] [Model K] (p q : K) (c : Length) :
    ∃ d : Length, Proportion p q c d :=
  ⟨Length.mk' (val q * val c / val p) (div_pos (mul_pos (pos q) (pos c)) (pos p)),
    proportion_iff_mul.mpr (by simp; field_simp [(pos p).ne'])⟩

/-- Prop. 6.13: to find a mean proportional to two lines. -/
theorem Length.mean (a b : Length) : ∃ c : Length, Proportion a c c b := by
  obtain ⟨x, hx, hxx⟩ := exists_mul_self (mul_pos (pos a) (pos b))
  exact ⟨Length.mk' x hx, proportion_iff_mul.mpr (by simp [hxx])⟩

/-- Prop. 2.14: to construct a square equal to a given area. -/
theorem Area.side (A : Area) : ∃ x : Length, sq x = A := by
  obtain ⟨x, hx, hxx⟩ := exists_mul_self (pos A)
  exact ⟨Length.mk' x hx, Model.ext (by simp [hxx])⟩

/-- Prop. 1.44: to apply to a given line a rectangle equal to a given area. -/
theorem Area.apply (a : Length) (A : Area) : ∃ x : Length, rect a x = A :=
  ⟨Length.mk' (val A / val a) (div_pos (pos A) (pos a)),
    Model.ext (by simp; field_simp [(pos a).ne'])⟩

/-- Prop. 6.28: to apply to a line `a`, cut in half at `h`, a rectangle equal to an area
`A` not greater than the square on the half, falling short by a square: `a` is cut into
`x` and `y` with `rect x y = A`. -/
theorem Area.apply_short {a h : Length} {A : Area} (ha : h + h = a) (hA : A ≤ sq h) :
    ∃ x y : Length, x + y = a ∧ rect x y = A := by
  have ha' : val h + val h = val a := by rw [← Model.val_add, ha]
  have hA' : val A ≤ val h * val h := by
    rw [← val_sq]; exact not_lt.mp (fun h' => not_lt.mpr hA (val_lt.mp h'))
  rcases hA'.lt_or_eq with hlt | heq
  · obtain ⟨t, ht, htt⟩ := exists_mul_self (sub_pos.mpr hlt)
    have hth : t < val h := by nlinarith [pos A, pos h]
    refine ⟨Length.mk' (val h + t) (by linarith [pos h]),
      Length.mk' (val h - t) (by linarith), Model.ext ?_, Model.ext ?_⟩ <;>
      simp <;> nlinarith
  · exact ⟨h, h, ha, Model.ext (by simp [heq])⟩

/-- Prop. 6.29: to apply to a line `a` a rectangle equal to an area `A`, exceeding by a
square: a line `x` with `rect (a + x) x = A`. -/
theorem Area.apply_excess (a : Length) (A : Area) : ∃ x : Length, rect (a + x) x = A := by
  -- `x * x + a * x = A`: `(2 * x + a) ^ 2 = 4 * A + a * a`
  obtain ⟨u, hu, huu⟩ :=
    exists_mul_self (by nlinarith [pos A, pos a] : 0 < 4 * val A + val a * val a)
  have hua : val a < u := by nlinarith [pos A, pos a]
  exact ⟨Length.mk' ((u - val a) / 2) (by linarith), Model.ext (by simp; nlinarith)⟩

/-- Props. 3.31 and 1.47 (the lemma after 10.13): for unequal lines, a line on which the
square is the excess of the square on the greater over that on the lesser. -/
theorem Length.exceeds {a b : Length} (h : b < a) : ∃ c : Length, sq b + sq c = sq a := by
  have h' : val b < val a := val_lt.mpr h
  obtain ⟨c, hc, hcc⟩ :=
    exists_mul_self (by nlinarith [pos b] : 0 < val a * val a - val b * val b)
  exact ⟨Length.mk' c hc, Model.ext (by simp; linarith)⟩

end Elements.Book10
