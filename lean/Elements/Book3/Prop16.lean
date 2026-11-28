import SystemE
import Elements.Book1.Prop05
import Elements.Book1.Prop12
import Elements.Book1.Prop17
import Elements.Book1.Prop19
import Elements.Book1.Prop23

namespace Elements.Book3

/-
Prop. 3.16. `AB` is a diameter of a circle with center `D`, and `AE` is at right
angles to it at `A`. Euclid's further claims, that the angle of the semicircle is
greater, and the remaining (horn) angle between the circle and `AE` less, than any acute
rectilinear angle, are about angles contained by a curve; System E has only rectilinear
angles, and they are left out. What makes them true is `proposition_16'`: no straight
line falls between `AE` and the circle.
-/

/-- A point `C` of `AE` other than `A` is not on the circle. -/
theorem proposition_16_on : ∀ (a b c d e : Point) (AE : Line) (α : Circle),
  a.onCircle α ∧ b.onCircle α ∧ d.isCentre α ∧ between a d b ∧
  a.onLine AE ∧ e.onLine AE ∧ e ≠ a ∧ ∠ b:a:e = ∟ ∧ c.onLine AE ∧ c ≠ a →
  ¬(c.onCircle α) :=
by
  euclid_intros
  -- if possible, let it fall like CA, and let DC be joined
  euclid_apply (line_from_points a b) as AB
  euclid_apply (line_from_points d c) as DC
  -- Missed by Euclid: B is off AE, the angle BAE being right.
  have : (0 : ℝ) < ∠ b:a:e := by linarith [Elements.Book1.right_angle_pos]
  euclid_apply (Elements.Book1.not_on_line_of_angle b a e AB AE)
  -- DA = DC, so the angles DAC, ACD are equal [Prop. 1.5]; and DAC is right
  euclid_apply (point_on_circle_onlyif d a c α)
  euclid_apply (right_angle_on_lines b a e d c AB AE)
  euclid_apply (Elements.Book1.proposition_5' d a c AB AE DC)
  -- so the triangle ACD has two right angles [Prop. 1.17]
  euclid_apply (Elements.Book1.proposition_17 d a c AB AE DC)
  euclid_finish

/-- The straight line `AE` at right angles to the diameter `AB` at `A` falls outside. -/
theorem proposition_16 : ∀ (a b c d e : Point) (AE : Line) (α : Circle),
  a.onCircle α ∧ b.onCircle α ∧ d.isCentre α ∧ between a d b ∧
  a.onLine AE ∧ e.onLine AE ∧ e ≠ a ∧ ∠ b:a:e = ∟ ∧ c.onLine AE ∧ c ≠ a →
  c.outsideCircle α :=
by
  euclid_intros
  euclid_apply (proposition_16_on a b c d e AE α)
  -- similarly, it does not fall inside: then AE would meet the circle again
  by_cases (c.insideCircle α)
  · euclid_apply (intersection_circle_line_extending_points α AE c a) as c'
    euclid_apply (proposition_16_on a b c' d e AE α)
    exfalso
    euclid_finish
  · euclid_finish

/-- No other straight line `AF` falls between `AE` and the circle: it cuts the circle. -/
theorem proposition_16' : ∀ (a b d e : Point) (AE AF : Line) (α : Circle),
  a.onCircle α ∧ b.onCircle α ∧ d.isCentre α ∧ between a d b ∧
  a.onLine AE ∧ e.onLine AE ∧ e ≠ a ∧ ∠ b:a:e = ∟ ∧ a.onLine AF ∧ AF ≠ AE →
  AF.intersectsCircle α :=
by
  euclid_intros
  by_cases (d.onLine AF)
  · -- Missed by Euclid: AF is the diameter.
    euclid_finish
  · -- DG perpendicular to FA [Prop. 1.12]
    euclid_apply (line_from_points a b) as AB
    euclid_apply (exists_distincts_points_on_line AF a) as f
    euclid_apply (Elements.Book1.proposition_12 a f d AF) as g
    have : (0 : ℝ) < ∠ b:a:e := by linarith [Elements.Book1.right_angle_pos]
    euclid_apply (Elements.Book1.not_on_line_of_angle b a e AB AE)
    by_cases (g = a)
    · -- Missed by Euclid: G is not A, for then AF, too, would be at right angles to AB.
      exfalso
      rcases ‹_ ∨ _› with ⟨_, _⟩ | ⟨_, _⟩
      · euclid_finish
      · euclid_apply (right_angle_on_lines f a d f b AF AB)
        by_cases (f.sameSide e AB)
        · euclid_apply (on_line_of_eq_angle f AE a e b AB)
          euclid_finish
        · euclid_apply (extend_point AE e a) as e'
          euclid_apply (right_angle_on_lines b a e b e' AB AE)
          euclid_apply (on_line_of_eq_angle f AE a e' b AB)
          euclid_finish
    · euclid_apply (line_from_points g d) as GD
      have : ∠ a:g:d = ∟ := by
        rcases ‹_ ∨ _› with ⟨_, _⟩ | ⟨_, _⟩
        · euclid_finish
        · euclid_apply (right_angle_on_lines f g d a d AF GD)
          euclid_finish
      -- AGD is right, so DAG is less than a right angle [Prop. 1.17], and AD is
      -- greater than DG [Prop. 1.19]
      euclid_apply (Elements.Book1.proposition_17 d g a GD AF AB)
      euclid_apply (Elements.Book1.proposition_19 d g a GD AF AB)
      -- so G is inside the circle, and AF cuts it
      euclid_apply (point_in_circle_if d a g α)
      euclid_apply (intersection_circle_line_2 g α AF)
      euclid_finish

/-- Corollary: the straight line `AE` at right angles to a diameter at its end touches
the circle. -/
theorem proposition_16_corollary : ∀ (a b d e : Point) (AE : Line) (α : Circle),
  a.onCircle α ∧ b.onCircle α ∧ d.isCentre α ∧ between a d b ∧
  a.onLine AE ∧ e.onLine AE ∧ e ≠ a ∧ ∠ b:a:e = ∟ → AE.touchesCircleAt α a :=
by
  euclid_intros
  -- Missed by Euclid: if AE cut the circle, it would meet it at a point other than A.
  refine ⟨‹_›, ‹_›, ?_⟩
  intro
  euclid_apply (intersections_circle_line α AE) as (p, q)
  by_cases (p = a)
  · euclid_apply (proposition_16 a b q d e AE α)
    euclid_finish
  · euclid_apply (proposition_16 a b p d e AE α)
    euclid_finish

end Elements.Book3
