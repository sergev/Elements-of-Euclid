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

/-- The other half of `between_trans_in`; by cases on `between_points`. -/
theorem between_trans_in' : ∀ (a b c d : Point),
    between a b c ∧ between a d b → between d b c := by
  intro a b c d ⟨habc, hadb⟩
  have ⟨hcba, hab, _, _⟩ := between_symm a b c habc
  have ⟨_, hcb, _, nbca⟩ := between_symm c b a hcba
  have ⟨hbda, _, _, _⟩ := between_symm a d b hadb
  have ⟨_, hbd, _, _⟩ := between_symm b d a hbda
  have ⟨hcda, _, _, _⟩ := between_symm a d c (between_trans_in a b c d ⟨habc, hadb⟩)
  have ⟨_, hcd, _, _⟩ := between_symm c d a hcda
  obtain ⟨L, haL, hbL⟩ := line_from_points a b hab
  have hcL := between_same_line_out a b c L ⟨habc, haL, hbL⟩
  have hdL := between_same_line_in a d b L ⟨hadb, haL, hbL⟩
  rcases between_points d b c L ⟨hbd.symm, hcb.symm, hcd, hdL, hbL, hcL⟩ with h | h | h
  · exact h
  · exact absurd hcda (between_not_trans b d c a ⟨h, hbda⟩)
  · exact absurd (between_trans_in b d a c ⟨hbda, (between_symm d c b h).1⟩) nbca

/-- Of two points on a segment from `a`, the nearer is between `a` and the other. -/
theorem between_of_lt : ∀ (a x y e : Point),
    between a x e ∧ between a y e ∧ |(a─x)| < |(a─y)| → between a x y := by
  intro a x y e ⟨hx, hy, hlt⟩
  have ⟨hex, hax, hae, _⟩ := between_symm a x e hx
  have ⟨_, hay, _, _⟩ := between_symm a y e hy
  have hxy : x ≠ y := fun h => by subst h; exact lt_irrefl _ hlt
  obtain ⟨L, haL, heL⟩ := line_from_points a e hae
  have hxL := between_same_line_in a x e L ⟨hx, haL, heL⟩
  have hyL := between_same_line_in a y e L ⟨hy, haL, heL⟩
  rcases between_points a x y L ⟨hax, hxy, hay.symm, haL, hxL, hyL⟩ with h | h | h
  · exact h
  · -- a between x and y: then a is between y and e
    have := between_trans_out y a x e ⟨(between_symm x a y h).1, hx⟩
    exact absurd hy (between_symm y a e this).2.2.2
  · have := between_if a y x h
    have := segment_gte_zero (y─x)
    linarith

/-- An angle whose sides are on different lines is positive. -/
theorem angle_pos_of_not_on_line : ∀ (a b c : Point) (L : Line),
    a ≠ b ∧ a ≠ c ∧ a.onLine L ∧ b.onLine L ∧ ¬(c.onLine L) → 0 < ∠ b:a:c := by
  intro a b c L ⟨hab, hac, haL, hbL, hcL⟩
  refine lt_of_le_of_ne (angle_range _).1 fun h => hcL ?_
  exact (degenerated_angle_onlyif a b c L ⟨hab, hac, haL, hbL, h.symm⟩).1

/-- A point equidistant from two points of its line is between them. -/
theorem between_of_eq_dist : ∀ (a m b : Point) (L : Line),
    a.onLine L ∧ m.onLine L ∧ b.onLine L ∧ a ≠ b ∧ |(a─m)| = |(b─m)| → between a m b := by
  intro a m b L ⟨haL, hmL, hbL, hab, h⟩
  have s1 := segment_symmetric a m
  have s2 := segment_symmetric b m
  have s3 := segment_symmetric a b
  have hpos : 0 < |(a─b)| := lt_of_le_of_ne (segment_gte_zero _) fun h0 => hab (zero_segment_if a b h0.symm)
  have ham : a ≠ m := fun e => by
    subst e
    have := zero_segment_onlyif a a rfl
    exact hab (zero_segment_if b a (by linarith)).symm
  have hbm : m ≠ b := fun e => by
    subst e
    have := zero_segment_onlyif m m rfl
    exact hab (zero_segment_if a m (by linarith))
  rcases between_points a m b L ⟨ham, hbm, hab.symm, haL, hmL, hbL⟩ with h1 | h1 | h1
  · exact h1
  · have := between_if m a b h1
    linarith
  · have := between_if a b m h1
    linarith

/-- Two points on the other side from a third are on the same side. -/
theorem same_side_of_opposite : ∀ (a b c : Point) (L : Line),
    ¬(a.onLine L) ∧ ¬(b.onLine L) ∧ ¬(c.onLine L) ∧ ¬(a.sameSide b L) ∧ ¬(a.sameSide c L) →
    b.sameSide c L := by
  intro a b c L ⟨ha, hb, hc, hab, hac⟩
  rcases same_side_pigeon_hole a b c L ⟨ha, hb, hc⟩ with h | h | h
  · exact absurd h hab
  · exact absurd h hac
  · exact h

/-- Two points of a line that does not meet `L` are on the same side of `L`. -/
theorem same_side_of_parallel : ∀ (a b : Point) (L M : Line),
    a.onLine M ∧ b.onLine M ∧ ¬(a.onLine L) ∧ ¬(M.intersectsLine L) → a.sameSide b L := by
  intro a b L M ⟨ha, hb, haL, hML⟩
  have hbL : ¬(b.onLine L) := fun h =>
    hML (intersection_lines_common_point b M L ⟨hb, h, fun e => haL (e ▸ ha)⟩)
  by_contra h
  exact hML (intersection_symm _ _ (intersection_lines_opposing a b L M ⟨⟨haL, hbL, h⟩, ha, hb⟩))

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
    ``not_inside_circle_of_ge, ``not_on_circle_of_gt, ``not_on_circle_of_lt,
    ``between_trans_in', ``angle_pos_of_not_on_line,
    ``same_side_of_opposite, ``same_side_of_parallel]
  backwardLemmas := #[
    ``ne_of_lines_ne, ``not_between_of_same_side, ``not_on_line_of_triangle,
    ``eq_of_same_ray, ``on_line_of_eq_angle]
  guardedLemmas := #[``between_of_lt, ``between_of_eq_dist]
  linarith := fun hyps e => do
    let m ← mkFreshExprMVar e
    try
      Mathlib.Tactic.Linarith.linarith true hyps {} m.mvarId!
      return some (← instantiateMVars m)
    catch _ => return none }

end SystemE.Saturate
