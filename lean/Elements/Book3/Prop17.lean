import SystemE
import Elements.Book1.Prop04
import Elements.Book1.Prop11
import Elements.Book3.Prop16

namespace Elements.Book3

/-- To draw a straight line `AB` touching a given circle from a given point `A` outside. -/
theorem proposition_17 : ∀ (a e : Point) (α : Circle),
  a.outsideCircle α ∧ e.isCentre α →
  ∃ (b : Point) (AB : Line), a.onLine AB ∧ AB.touchesCircleAt α b :=
by
  euclid_intros
  -- join AE, meeting the circle at D; draw the circle AFG with center E and radius EA
  euclid_apply (line_from_points e a) as EA
  euclid_apply (intersection_circle_line_between_points α EA e a) as d
  euclid_apply (circle_from_points e a) as AFG
  -- DF at right angles to EA [Prop. 1.11]
  euclid_apply (Elements.Book1.proposition_11 e a d EA) as x
  euclid_apply (line_from_points d x) as DF
  -- Missed by Euclid: D is inside AFG, so DF meets it at F; and EF meets BCD at B.
  euclid_apply (between_if e d a)
  euclid_apply (point_in_circle_if e a d AFG)
  euclid_apply (intersection_circle_line_2 d AFG DF)
  euclid_apply (intersections_circle_line AFG DF) as (f, f')
  euclid_apply (line_from_points e f) as EF
  euclid_apply (point_on_circle_onlyif e a f AFG)
  euclid_apply (intersection_circle_line_between_points α EF e f) as b
  euclid_apply (point_on_circle_onlyif e d b α)
  euclid_apply (line_from_points a b) as AB
  -- EA = EF and ED = EB, with the angle at E common: the angle EBA is equal to EDF,
  -- a right angle [Prop. 1.4]
  euclid_apply (equal_angles e a d b f EA EF)
  euclid_apply (Elements.Book1.proposition_4 e a b e f d EA AB EF EF DF EA)
  euclid_apply (right_angle_on_lines e d x e f EA DF)
  -- EB is a radius, and AB is at right angles to it at B: AB touches the circle
  -- [Prop. 3.16 corollary]
  euclid_apply (intersection_circle_line_extending_points α EF e b) as b'
  euclid_apply (equal_angles b e b' a a EF AB)
  euclid_apply (proposition_16_corollary b b' e a AB α)
  use b, AB

end Elements.Book3
