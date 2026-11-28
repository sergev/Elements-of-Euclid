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

/-- A magnitude is not greater than any multiple of it. -/
theorem le_mult (n : ℕ+) (a : M) : a ≤ n • a :=
  mult_le_mult_left a (PNat.coe_le_coe 1 n |>.mp n.pos)

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
  exact le_mult n a

theorem Commensurable.refl (a : M) : Commensurable a a := ⟨a, .refl a, .refl a⟩

theorem Commensurable.symm {a b : M} (h : Commensurable a b) : Commensurable b a :=
  let ⟨c, h₁, h₂⟩ := h; ⟨c, h₂, h₁⟩

theorem Commensurable.of_measures {a b : M} (h : Measures a b) : Commensurable a b :=
  ⟨a, .refl a, h⟩

theorem not_commensurable_symm {a b : M} (h : ¬ Commensurable a b) :
    ¬ Commensurable b a := fun h' => h h'.symm

/-- The greater multiple of a magnitude is greater, and conversely. -/
theorem mult_lt_mult_iff {m n : ℕ+} {a : M} : m • a < n • a ↔ m < n :=
  ⟨lt_of_mult_lt_mult_left, mult_lt_mult_left a⟩

/--
Def. 7.20 for magnitudes: if `c` measures `a` as many times as `u` measures `d`, then as
`c` is to `a`, so `u` is to `d`. Euclid takes it from Def. 7.20 (10.5, 10.6, with `u` the
unit and `d` a number); here it is proved from Def. 5.5.
-/
theorem proportion_mult {N : Type*} [Magnitude N] (m : ℕ+) (c : M) (u : N) :
    Proportion c (m • c) u (m • u) := by
  refine ⟨fun k l => ?_, fun k l => ?_, fun k l => ?_⟩
  · rw [Elements.Book5.proposition_3, Elements.Book5.proposition_3, mult_lt_mult_iff,
      mult_lt_mult_iff]
  · rw [Elements.Book5.proposition_3, Elements.Book5.proposition_3]
    exact ⟨fun h => congrArg (· • u) (mult_inj_left h),
      fun h => congrArg (· • c) (mult_inj_left h)⟩
  · rw [Elements.Book5.proposition_3, Elements.Book5.proposition_3, mult_lt_mult_iff,
      mult_lt_mult_iff]

/-- If `a ∶ b ∷ c ∶ d`, all of one kind, and the first is greater than the second, the
third is greater than the fourth [Props. 5.16, 5.14]. -/
theorem lt_of_proportion {a b c d : M} (h : Proportion a b c d) (hba : b < a) : d < c :=
  (Elements.Book5.proposition_14 (Elements.Book5.proposition_16 h)).1 hba

/-- Two magnitudes are the mean proportional of the same two only if equal: of unequal
means, the lesser has the greater ratio to it from the first [Prop. 5.8], and the smaller
to the last [Prop. 5.8], which cannot both be [Props. 5.13, 5.10]. -/
theorem mean_proportional_unique {a b x y : M} (hx : Proportion a x x b)
    (hy : Proportion a y y b) : x = y := by
  have key : ∀ {x y : M}, Proportion a x x b → Proportion a y y b → ¬ x < y := by
    intro x y hx hy hlt
    have h₁ := Elements.Book5.proposition_13' (Elements.Book5.proposition_8 hlt a).2 hy
    have h₂ := Elements.Book5.proposition_13 hx.symm h₁
    exact Elements.Book5.proposition_10_lemma (Elements.Book5.proposition_8 hlt b).1 h₂
  rcases lt_trichotomy x y with h | h | h
  · exact absurd h (key hx hy)
  · exact h
  · exact absurd h (key hy hx)

/-- Prop. 5.12 for two: if `a ∶ b ∷ c ∶ d`, then `a ∶ b ∷ a + c ∶ b + d`. -/
theorem proportion_add {a b c d : M} (h : Proportion a b c d) :
    Proportion a b (a + c) (b + d) :=
  Elements.Book5.proposition_12 (n := 1) (a := fun i => if i = 0 then a else c)
    (b := fun i => if i = 0 then b else d) (fun i => by
      match i with
      | ⟨0, _⟩ => exact Proportion.refl a b
      | ⟨1, _⟩ => exact h)

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

/-- Lines on which the squares are equal are equal. -/
theorem sq_inj {a b : Length} (h : sq a = sq b) : a = b := by
  have h' : val a * val a = val b * val b := by rw [← val_sq, ← val_sq, h]
  have := pos a; have := pos b
  exact Model.ext (by nlinarith)

/-- The greater line has the greater square. -/
theorem sq_lt_sq {a b : Length} : sq a < sq b ↔ a < b := by
  rw [← val_lt, ← val_lt, val_sq, val_sq]
  have := pos a; have := pos b
  constructor <;> intro h <;> nlinarith

/-- Of rectangles on the same side, the one with the greater other side is greater. -/
theorem rect_lt_rect {a b c : Length} : rect c a < rect c b ↔ a < b := by
  rw [← val_lt, ← val_lt, val_rect, val_rect]
  exact mul_lt_mul_iff_of_pos_left (pos c)

/-- Equal rectangles on the same side have equal other sides. -/
theorem rect_inj {a b c : Length} (h : rect c a = rect c b) : a = b := by
  have h' : val c * val a = val c * val b := by rw [← val_rect, ← val_rect, h]
  exact Model.ext (mul_left_cancel₀ (pos c).ne' h')

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

/-- Prop. 2.4, the line cut in half: the square on `t + t` is four times the square on
`t`. -/
theorem sq_double (t : Length) : sq (t + t) = (4 : ℕ+) • sq t :=
  Model.ext (by simp; ring)

/-- Prop. 2.5: a line `e + e` cut in half and unequally, into `x = e + t` and `y`, with
`y + t = e`: the rectangle contained by the unequal pieces, with the square on the line
between the cuts, is the square on the half. -/
theorem rect_add_sq {x y e t : Length} (hx : e + t = x) (hy : y + t = e) :
    rect x y + sq t = sq e := by
  subst hx hy; exact Model.ext (by simp; ring)

/-- Prop. 2.9: a line `e + e` cut in half and unequally, into `x = e + t` and `y`, with
`y + t = e`: the squares on the unequal pieces are double the squares on the half and on
the line between the cuts. -/
theorem sq_add_sq_half {x y e t : Length} (hx : e + t = x) (hy : y + t = e) :
    sq x + sq y = (2 : ℕ+) • (sq e + sq t) := by
  subst hx hy; exact Model.ext (by simp; ring)

/-- Prop. 6.14: equal rectangles have their sides reciprocally proportional. -/
theorem proportion_of_rect_eq {a b c d : Length} (h : rect a b = rect c d) :
    Proportion a c d b := by
  have h' : val a * val b = val c * val d := by rw [← val_rect, ← val_rect, h]
  exact proportion_iff_mul.mpr h'

/-- Prop. 6.17: if three lines are proportional, the rectangle contained by the outer is
the square on the middle. -/
theorem rect_eq_sq_of_proportion {a b c : Length} (h : Proportion a b b c) :
    rect a c = sq b :=
  Model.ext (by simpa using proportion_iff_mul.mp h)

/-- Prop. 6.16: if four lines are proportional, the rectangle contained by the outer is
the rectangle contained by the middle. -/
theorem rect_eq_of_proportion {a b c d : Length} (h : Proportion a b c d) :
    rect a d = rect b c :=
  Model.ext (by simpa using proportion_iff_mul.mp h)

/-- Props. 6.8, 6.4 and 6.8's corollary: in a right-angled triangle with legs `u`, `v` and
base `l`, the perpendicular `p` from the right angle cutting the base into `m` (by `u`)
and `n`, the triangles are similar to the whole and to one another: `l` is to `u` as `u`
to `m`, and to `v` as `v` to `n`; the perpendicular is the mean proportional of `m` and
`n`; and `l` is to `v` as `u` to `p`. The right angles are given by the squares (1.47). -/
theorem right_triangle_proportions {l u v m n p : Length} (hmn : m + n = l)
    (hu : sq p + sq m = sq u) (hv : sq p + sq n = sq v) (hl : sq u + sq v = sq l) :
    Proportion l u u m ∧ Proportion l v v n ∧ Proportion m p p n ∧
      Proportion l v u p := by
  have hmn' : val m + val n = val l := by rw [← Model.val_add, hmn]
  have hu' : val p * val p + val m * val m = val u * val u := by
    rw [← val_sq, ← val_sq, ← val_sq, ← Model.val_add, hu]
  have hv' : val p * val p + val n * val n = val v * val v := by
    rw [← val_sq, ← val_sq, ← val_sq, ← Model.val_add, hv]
  have hl' : val u * val u + val v * val v = val l * val l := by
    rw [← val_sq, ← val_sq, ← val_sq, ← Model.val_add, hl]
  have hp : val p * val p = val m * val n := by rw [← hmn'] at hl'; nlinarith
  have hlm : val l * val m = val u * val u := by rw [← hmn']; nlinarith
  have hln : val l * val n = val v * val v := by rw [← hmn']; nlinarith
  have hlp : val l * val p = val u * val v := by
    have := pos l; have := pos p; have := pos u; have := pos v
    have hsq : (val l * val p) * (val l * val p) = (val u * val v) * (val u * val v) := by
      linear_combination
        (val l * val l) * hp + (val l * val n) * hlm + (val u * val u) * hln
    rcases mul_self_eq_mul_self_iff.mp hsq with h | h
    · exact h
    · nlinarith [mul_pos ‹0 < val l› ‹0 < val p›, mul_pos ‹0 < val u› ‹0 < val v›]
  exact ⟨proportion_iff_mul.mpr hlm, proportion_iff_mul.mpr hln,
    proportion_iff_mul.mpr hp.symm, proportion_iff_mul.mpr (hlp.trans (mul_comm _ _))⟩

/-! The constructions by which Euclid finds lines, in the model. -/

/-- Prop. 6.9: to cut off a prescribed part from a line, the `n`th part. -/
theorem Length.part (a : Length) (n : ℕ+) : ∃ c : Length, a = n • c := by
  have hn : (0 : ℝ) < n := by exact_mod_cast n.pos
  exact ⟨Length.mk' (val a / n) (div_pos (pos a) hn), Model.ext (by simp; field_simp)⟩

/-- Magnitudes of a kind that can be divided into any number of equal parts, as Euclid
divides a magnitude in 10.6: lines by Prop. 6.9 (`Length.divisible`), areas by applying
them to a line and dividing the breadth (`Area.divisible`). -/
def Divisible (K : Type*) [Magnitude K] : Prop := ∀ (a : K) (n : ℕ+), ∃ c, a = n • c

theorem Length.divisible : Divisible Length := Length.part

/-- An area divided into equal parts: applied to a line (1.44), the breadth divided
(6.9). -/
theorem Area.divisible : Divisible Area := fun A n => by
  have hn : (0 : ℝ) < n := by exact_mod_cast n.pos
  exact ⟨Area.mk' (val A / n) (div_pos (pos A) hn), Model.ext (by simp; field_simp)⟩

/-- Prop. 6.12: to find a fourth proportional to two magnitudes and a line: as `p` to
`q`, so `c` to some line. For areas `p`, `q` Euclid applies them to a line first (6.1). -/
theorem Length.fourth' {K : Type} [Magnitude K] [Model K] (p q : K) (c : Length) :
    ∃ d : Length, Proportion p q c d :=
  ⟨Length.mk' (val q * val c / val p) (div_pos (mul_pos (pos q) (pos c)) (pos p)),
    proportion_iff_mul.mpr (by simp; field_simp [(pos p).ne'])⟩

/-- A fourth proportional to two magnitudes and an area [Prop. 6.12, the areas applied to
a line, 6.1]. -/
theorem Area.fourth' {K : Type} [Magnitude K] [Model K] (p q : K) (c : Area) :
    ∃ d : Area, Proportion p q c d :=
  ⟨Area.mk' (val q * val c / val p) (div_pos (mul_pos (pos q) (pos c)) (pos p)),
    proportion_iff_mul.mpr (by simp; field_simp [(pos p).ne'])⟩

/-- Prop. 6.10: to cut a line `e` in a given ratio, of `m` to `n`. -/
theorem Length.cut {K : Type} [Magnitude K] [Model K] (e : Length) (m n : K) :
    ∃ s t : Length, s + t = e ∧ Proportion m n s t := by
  have hm := pos m; have hn := pos n; have he := pos e
  refine ⟨Length.mk' (val e * val m / (val m + val n)) (by positivity),
    Length.mk' (val e * val n / (val m + val n)) (by positivity), Model.ext ?_,
    proportion_iff_mul.mpr ?_⟩ <;> simp <;> field_simp

/-- Prop. 6.12, for 10.112: to produce a line `f` by `q`, so that as `h` is to `f`, so is
the whole `f + q` to `q`; `h` greater than `f`. (`q` is the fourth proportional to the
excess of `h` over `f`, `f`, and `f`.) -/
theorem Length.extend {h f : Length} (hf : f < h) :
    ∃ q : Length, Proportion h f (f + q) q := by
  have h' : val f < val h := val_lt.mpr hf
  have hf0 := pos f
  refine ⟨Length.mk' (val f * val f / (val h - val f)) (div_pos (by positivity)
    (by linarith)), proportion_iff_mul.mpr ?_⟩
  simp
  have : val h - val f ≠ 0 := by linarith
  field_simp
  ring

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

/-- Prop. 1.47 (the lemma after 10.13): for two lines, the line on which the square is
the squares on both. -/
theorem Length.hypotenuse (a b : Length) : ∃ c : Length, sq a + sq b = sq c := by
  obtain ⟨c, hc, hcc⟩ :=
    exists_mul_self (by nlinarith [pos a, pos b] : 0 < val a * val a + val b * val b)
  exact ⟨Length.mk' c hc, Model.ext (by simp; linarith)⟩

/-- Props. 3.31, 1.11, 1.47: on the line `l`, cut into `x` and `y`, the semicircle; the
perpendicular `p` at the cut meets it, and the lines `u`, `v` joined to the ends are the
legs of a right-angled triangle on `l`, with `x` and `y` the pieces of the base. -/
theorem Length.semicircle {l x y : Length} (hxy : x + y = l) :
    ∃ u v p : Length, sq p + sq x = sq u ∧ sq p + sq y = sq v ∧ sq u + sq v = sq l := by
  obtain ⟨p, hp, hpp⟩ := exists_mul_self (mul_pos (pos x) (pos y))
  obtain ⟨u, hu, huu⟩ := exists_mul_self (mul_pos (pos l) (pos x))
  obtain ⟨v, hv, hvv⟩ := exists_mul_self (mul_pos (pos l) (pos y))
  have hl : val x + val y = val l := by rw [← Model.val_add, hxy]
  refine ⟨Length.mk' u hu, Length.mk' v hv, Length.mk' p hp, Model.ext ?_, Model.ext ?_,
    Model.ext ?_⟩ <;> simp only [Model.val_add, val_sq, val_length_mk]
  · linear_combination hpp - huu + val x * hl
  · linear_combination hpp - hvv + val y * hl
  · linear_combination huu + hvv + val l * hl

end Elements.Book10
