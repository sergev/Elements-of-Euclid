import SystemE
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Positive.Ring
import Mathlib.Tactic.LinearCombination
import Elements.Book5.Magnitude

/-
Magnitudes in the plane: lengths and areas of System E as magnitudes, so that Book 6 can
take their ratios with Book 5's propositions. System E measures them by reals; a length
or an area here is a positive real, and the instance is on all positive reals.
-/

namespace Elements.Book5

open Magnitude

/--
The positive reals are a kind of magnitude. Def. 5.4 holds since the reals are
Archimedean: a fact of the model, not one Euclid proves.
-/
noncomputable instance : Magnitude {x : ℝ // 0 < x} where
  lt_add a b := by
    show a.val < (a + b).val
    rw [Positive.coe_add]
    linarith [b.2]
  remainder a b h := ⟨⟨b.val - a.val, sub_pos.mpr h⟩, Subtype.ext (by
    rw [Positive.coe_add]
    ring)⟩
  ratio a b := by
    have hval : ∀ n : ℕ, ((· + a)^[n] a).val = (n + 1) * a.val := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Function.iterate_succ_apply', Positive.coe_add, ih]
        push_cast
        ring
    obtain ⟨n, hn⟩ := exists_nat_gt (b.val / a.val)
    refine ⟨n, ?_⟩
    show b.val < ((· + a)^[n] a).val
    rw [hval, ← div_lt_iff₀ a.2]
    linarith

namespace Positive

/-- A multiple `n • x` of a positive real is `n * x`. -/
theorem mult_val (n : ℕ+) (x : {x : ℝ // 0 < x}) : (n • x).val = n * x.val := by
  induction n using PNat.recOn with
  | one => simp [one_mult]
  | succ n ih =>
    rw [mult_succ, Positive.coe_add, ih]
    push_cast
    ring

/--
Positive reals `p`, `q`, `r`, `s` are proportional when `p * s = q * r`. A fact of the
model, used only for `fourth`.
-/
theorem proportion_of_mul_eq {p q r s : {x : ℝ // 0 < x}}
    (h : p.val * s.val = q.val * r.val) : Proportion p q r s := by
  have hp := p.2
  have hq := q.2
  have hr := r.2
  have hs := s.2
  refine ⟨fun m n => ?_, fun m n => ?_, fun m n => ?_⟩
  · show (n • q).val < (m • p).val ↔ (n • s).val < (m • r).val
    simp only [mult_val]
    have hm : (0 : ℝ) < m := by exact_mod_cast m.pos
    have hn : (0 : ℝ) < n := by exact_mod_cast n.pos
    constructor <;> intro h' <;> nlinarith
  · rw [Subtype.ext_iff, Subtype.ext_iff, mult_val, mult_val, mult_val, mult_val]
    have hm : (0 : ℝ) < m := by exact_mod_cast m.pos
    have hn : (0 : ℝ) < n := by exact_mod_cast n.pos
    constructor <;> intro h'
    · apply mul_right_cancel₀ (ne_of_gt hq)
      linear_combination s.val * h' - (m : ℝ) * h
    · apply mul_right_cancel₀ (ne_of_gt hs)
      linear_combination q.val * h' + (m : ℝ) * h
  · show (m • p).val < (n • q).val ↔ (m • r).val < (n • s).val
    simp only [mult_val]
    have hm : (0 : ℝ) < m := by exact_mod_cast m.pos
    have hn : (0 : ℝ) < n := by exact_mod_cast n.pos
    constructor <;> intro h' <;> nlinarith

/-- A fourth proportional to three positive reals exists (for Props. 5.18, 5.24). -/
theorem fourth (p q r : {x : ℝ // 0 < x}) : ∃ s, Proportion p q r s :=
  ⟨⟨q.val * r.val / p.val, div_pos (mul_pos q.2 r.2) p.2⟩,
    proportion_of_mul_eq (by field_simp [ne_of_gt p.2])⟩

end Positive

/-- Lengths, a kind of magnitude: positive reals. -/
def Length := {x : ℝ // 0 < x}

noncomputable instance : Magnitude Length := inferInstanceAs (Magnitude {x : ℝ // 0 < x})

/-- Areas, another kind: positive reals. -/
def Area := {x : ℝ // 0 < x}

noncomputable instance : Magnitude Area := inferInstanceAs (Magnitude {x : ℝ // 0 < x})

/-- Volumes, a third kind (Book 11): positive reals. -/
def Volume := {x : ℝ // 0 < x}

noncomputable instance : Magnitude Volume := inferInstanceAs (Magnitude {x : ℝ // 0 < x})

namespace Length

/-- The length of the straight line `ab`, `a ≠ b`. -/
noncomputable def of (a b : Point) (h : a ≠ b) : Length :=
  ⟨|(a─b)|, lt_of_le_of_ne (segment_gte_zero _) fun h' => h (zero_segment_if a b h'.symm)⟩

/-- Straight lines `ab` and `bc`, with `b` between `a` and `c`, together make `ac`. -/
theorem of_add {a b c : Point} (h : between a b c) (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) : of a b hab + of b c hbc = of a c hac :=
  Subtype.ext (by
    show |(a─b)| + |(b─c)| = |(a─c)|
    exact between_if a b c h)

/-- A fourth proportional to three lengths exists. -/
theorem fourth (p q r : Length) : ∃ s : Length, Proportion p q r s :=
  Positive.fourth p q r

end Length

namespace Area

/-- The area of the triangle `abc`, with `c` off the line `L` through `a` and `b`. -/
noncomputable def triangle (a b c : Point) (L : Line)
    (h : distinctPointsOnLine a b L ∧ ¬ c.onLine L) : Area :=
  ⟨Triangle.area △a:b:c, lt_of_le_of_ne (area_gte_zero _)
    fun h' => h.2 (degenerated_area_if a b c L ⟨h.1, h'.symm⟩)⟩

/-- A parallelogram has a positive area: `d` is off the line `ab`, parallel to `cd`. -/
theorem parallelogram_pos : ∀ (a b c d : Point) (AB CD AC BD : Line),
    formParallelogram a b c d AB CD AC BD → 0 < ▱ a:b:c:d := by
  euclid_intros
  euclid_assert ¬ d.onLine AB
  euclid_assert a ≠ b
  have h₁ : (△a:b:d).area ≠ 0 := fun h₀ => ‹¬ d.onLine AB›
    (degenerated_area_if a b d AB ⟨⟨‹a.onLine AB›, ‹b.onLine AB›, ‹a ≠ b›⟩, h₀⟩)
  have := area_gte_zero (△a:c:d)
  have := lt_of_le_of_ne (area_gte_zero (△a:b:d)) h₁.symm
  linarith

/-- The area of the parallelogram `abcd` (`formParallelogram`, sides `ab`, `cd`). -/
noncomputable def parallelogram (a b c d : Point) (AB CD AC BD : Line)
    (h : formParallelogram a b c d AB CD AC BD) : Area :=
  ⟨▱ a:b:c:d, parallelogram_pos a b c d AB CD AC BD h⟩

/-- A fourth proportional to three areas exists. -/
theorem fourth (p q r : Area) : ∃ s : Area, Proportion p q r s := Positive.fourth p q r

end Area

end Elements.Book5
