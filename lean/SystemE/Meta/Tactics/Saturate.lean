import Mathlib.Tactic.Linarith
import SystemE.Theory
import SaturateCore

/-!
Lemmas for saturation, proved from System E's axioms, and the engine's
configuration (see `SaturateCore`).
-/

open Lean Meta

theorem point_ne_symm : ∀ (a b : Point), a ≠ b → b ≠ a := fun _ _ h => h.symm

theorem length_pos_of_ne : ∀ (a b : Point), a ≠ b → 0 < |(a─b)| := fun a b h =>
  lt_of_le_of_ne (segment_gte_zero _) fun h0 => h (zero_segment_if a b h0.symm)

theorem ne_of_length_pos : ∀ (a b : Point), 0 < |(a─b)| → a ≠ b := by
  intro a b h e
  rw [zero_segment_onlyif a b e] at h
  exact lt_irrefl _ h

theorem not_inside_circle_of_ge : ∀ (a b c : Point) (α : Circle),
    (a.isCentre α) ∧ (b.onCircle α) ∧ |(a─b)| ≤ |(a─c)| → ¬(c.insideCircle α) := by
  intro a b c α ⟨ha, hb, h⟩ hc
  have := point_in_circle_onlyif a b c α ⟨ha, hb, hc⟩
  linarith

theorem not_on_circle_of_gt : ∀ (a b c : Point) (α : Circle),
    (a.isCentre α) ∧ (b.onCircle α) ∧ |(a─b)| < |(a─c)| → ¬(c.onCircle α) := by
  intro a b c α ⟨ha, hb, h⟩ hc
  have := point_on_circle_onlyif a b c α ⟨ha, hb, hc⟩
  linarith

theorem not_on_circle_of_lt : ∀ (a b c : Point) (α : Circle),
    (a.isCentre α) ∧ (b.onCircle α) ∧ |(a─c)| < |(a─b)| → ¬(c.onCircle α) := by
  intro a b c α ⟨ha, hb, h⟩ hc
  have := point_on_circle_onlyif a b c α ⟨ha, hb, hc⟩
  linarith

theorem ne_of_lines_ne : ∀ (a c b : Point) (L M : Line),
    a.onLine L ∧ b.onLine L ∧ b.onLine M ∧ c.onLine M ∧ a ≠ b ∧ L ≠ M → a ≠ c := by
  intro a c b L M ⟨haL, hbL, hbM, hcM, hab, hLM⟩ hac
  subst hac
  exact hLM (two_points_determine_line a b L M ⟨⟨haL, hbL, hab⟩, hcM, hbM⟩)

/-- A vertex of a triangle is not on the opposite side's line. -/
theorem not_on_line_of_triangle : ∀ (c a b : Point) (L M N : Line),
    a.onLine L ∧ b.onLine L ∧ c.onLine M ∧ b.onLine M ∧ c.onLine N ∧ a.onLine N ∧
    a ≠ b ∧ L ≠ M ∧ L ≠ N → ¬(c.onLine L) := by
  intro c a b L M N ⟨haL, hbL, hcM, hbM, hcN, haN, hab, hLM, hLN⟩ hcL
  have hac : a ≠ c := ne_of_lines_ne a c b L M ⟨haL, hbL, hbM, hcM, hab, hLM⟩
  exact hLN (two_points_determine_line a c L N ⟨⟨haL, hcL, hac⟩, haN, hcN⟩)

theorem not_between_of_same_side : ∀ (a b c : Point) (L : Line),
    a.sameSide c L ∧ b.onLine L → ¬(between a b c) :=
  fun a b c L ⟨h, hb⟩ hbtw => pasch_3 a b c L ⟨hbtw, hb⟩ h

/-- Points on the same ray from `d` at equal distances coincide. -/
theorem eq_of_same_ray : ∀ (x y d : Point) (L : Line),
    x.onLine L ∧ y.onLine L ∧ d.onLine L ∧ x ≠ d ∧ y ≠ d ∧ ¬(between x d y) ∧
    |(d─x)| = |(d─y)| → x = y := by
  intro x y d L ⟨hx, hy, hd, hxd, hyd, hb, h⟩
  by_contra hxy
  have := segment_symmetric d x
  have := segment_symmetric d y
  rcases between_points x d y L ⟨hxd, fun e => hyd e.symm, fun e => hxy e.symm, hx, hd, hy⟩
    with h1 | h1 | h1
  · exact hb h1
  · have := between_if d x y h1
    exact hxy (zero_segment_if x y (by linarith))
  · have := between_if x y d h1
    exact hxy (zero_segment_if x y (by linarith))

/-- Equal angles at `d` from line `L`, on the same side, lie on the same line. -/
theorem on_line_of_eq_angle : ∀ (c : Point) (M : Line) (d f e : Point) (L : Line),
    d.onLine M ∧ f.onLine M ∧ c.sameSide f L ∧ d.onLine L ∧ e.onLine L ∧
    d ≠ e ∧ d ≠ f ∧ d ≠ c ∧ ∠ e:d:c = ∠ e:d:f → c.onLine M := by
  intro c M d f e L ⟨hdM, hfM, hcf, hdL, heL, hde, hdf, hdc, hang⟩
  by_contra hcM
  have hfc := same_side_symm c f L hcf
  have hcL : ¬ c.onLine L := same_side_not_on_line c f L hcf
  have hfL : ¬ f.onLine L := same_side_not_on_line f c L hfc
  have hLM : L ≠ M := fun h => hfL (by rw [h]; exact hfM)
  obtain ⟨N, hdN, hcN⟩ := line_from_points d c hdc
  have hNM : N ≠ M := fun h => hcM (by rw [← h]; exact hcN)
  by_cases hs : e.sameSide c M
  · have hsum := sum_angles_onlyif d e f c L M
      ⟨hdL, hdM, heL, hfM, hde, hdf, hcL, hcM, hLM, hs, hfc⟩
    have h0 : ∠ c:d:f = 0 := by linarith
    have hfN := (degenerated_angle_onlyif d c f N ⟨hdc, hdf, hdN, hcN, h0⟩).1
    exact hNM (two_points_determine_line d f N M ⟨⟨hdN, hfN, hdf⟩, hdM, hfM⟩)
  · have hfN : ¬ f.onLine N := fun h =>
      hNM (two_points_determine_line d f N M ⟨⟨hdN, h, hdf⟩, hdM, hfM⟩)
    have hLN : L ≠ N := fun h => hcL (by rw [h]; exact hcN)
    have hef := triple_incidence_2 L M N d e f c
      ⟨hdL, hdM, hdN, heL, hfM, hcN, hfc, hs, hcM, fun h => hde h.symm⟩
    have hsum := sum_angles_onlyif d e c f L N
      ⟨hdL, hdN, heL, hcN, hde, hdc, hfL, hfN, hLN, hef, hcf⟩
    have h0 : ∠ f:d:c = 0 := by linarith
    exact hcM (degenerated_angle_onlyif d f c M ⟨hdf, hdc, hdM, hfM, h0⟩).1

theorem line_ne_symm : ∀ (L M : Line), L ≠ M → M ≠ L := fun _ _ h => h.symm

theorem circle_ne_symm : ∀ (α β : Circle), α ≠ β → β ≠ α := fun _ _ h => h.symm

theorem point_ne_of_on_line : ∀ (a b : Point) (L : Line),
    a.onLine L ∧ ¬(b.onLine L) → a ≠ b := fun _ _ _ ⟨h, hn⟩ e => hn (e ▸ h)

theorem line_ne_of_on_line : ∀ (a : Point) (L M : Line),
    a.onLine L ∧ ¬(a.onLine M) → L ≠ M := fun _ _ _ ⟨h, hn⟩ e => hn (e ▸ h)

theorem point_ne_of_on_circle : ∀ (a b : Point) (α : Circle),
    a.onCircle α ∧ ¬(b.onCircle α) → a ≠ b := fun _ _ _ ⟨h, hn⟩ e => hn (e ▸ h)

theorem circle_ne_of_on_circle : ∀ (a : Point) (α β : Circle),
    a.onCircle α ∧ ¬(a.onCircle β) → α ≠ β := fun _ _ _ ⟨h, hn⟩ e => hn (e ▸ h)

theorem point_ne_of_same_side : ∀ (a b c : Point) (L : Line),
    a.sameSide c L ∧ ¬(b.sameSide c L) → a ≠ b := fun _ _ _ _ ⟨h, hn⟩ e => hn (e ▸ h)

namespace SystemE.Saturate

initialize configRef.set {
  lemmas := #[
    ``point_ne_symm, ``line_ne_symm, ``circle_ne_symm,
    ``point_ne_of_on_line, ``line_ne_of_on_line, ``point_ne_of_on_circle,
    ``circle_ne_of_on_circle, ``point_ne_of_same_side,
    ``length_pos_of_ne, ``ne_of_length_pos,
    ``not_inside_circle_of_ge, ``not_on_circle_of_gt, ``not_on_circle_of_lt]
  backwardLemmas := #[
    ``ne_of_lines_ne, ``not_between_of_same_side, ``not_on_line_of_triangle,
    ``eq_of_same_ray, ``on_line_of_eq_angle]
  linarith := fun hyps e => do
    let m ← mkFreshExprMVar e
    try
      Mathlib.Tactic.Linarith.linarith true hyps {} m.mvarId!
      return some (← instantiateMVars m)
    catch _ => return none }

end SystemE.Saturate
