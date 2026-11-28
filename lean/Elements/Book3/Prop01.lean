import SystemE
import Elements.Book1.Prop08
import Elements.Book1.Prop10
import Elements.Book1.Prop11

namespace Elements.Book3

/--
Corollary to Prop. 3.1: a straight line `CE` cutting a chord `AB` in half at `D`, and at
right angles, passes through the center. It is the first half of the proof of 3.1, so it
comes first.
-/
theorem proposition_1_corollary : ∀ (a b c d o : Point) (AB CE : Line) (α : Circle),
  distinctPointsOnLine a b AB ∧ a.onCircle α ∧ b.onCircle α ∧
  between a d b ∧ |(a─d)| = |(d─b)| ∧ d.onLine CE ∧ c.onLine CE ∧ ¬(c.onLine AB) ∧
  ∠ a:d:c = ∟ ∧ o.isCentre α → o.onLine CE :=
by
  euclid_intros
  by_cases (o.onLine AB)
  · -- Missed by Euclid: a center on AB is D.
    euclid_apply (point_on_circle_onlyif o a b α)
    euclid_apply (between_of_eq_dist a o b AB)
    euclid_assert o = d
    euclid_finish
  · euclid_apply (line_from_points o d) as DG
    euclid_apply (line_from_points o a) as GA
    euclid_apply (line_from_points o b) as GB
    euclid_apply (point_on_circle_onlyif o a b α)
    -- AD = DB, DG common, GA = GB: the angles at D are equal [Prop. 1.8]
    euclid_apply (Elements.Book1.proposition_8 d a o d b o AB GA DG AB GB DG)
    euclid_apply (perpendicular_if a b d o AB)
    -- Missed by Euclid: two right angles at D are on one line.
    euclid_apply (extend_point CE c d) as e
    by_cases (o.sameSide c AB)
    · euclid_apply (on_line_of_eq_angle o CE d c a AB)
      euclid_finish
    · euclid_apply (right_angle_on_lines a d c a e AB CE)
      euclid_apply (on_line_of_eq_angle o CE d e a AB)
      euclid_finish

/-- A circle has a center (Def. 1.15); the proposition finds it. -/
theorem proposition_1 : ∀ (α : Circle) (o : Point), o.isCentre α → ∃ f : Point, f.isCentre α :=
by
  euclid_intros
  euclid_apply (exists_point_on_circle α) as a
  euclid_apply (exists_distinct_point_on_circle α a) as b
  euclid_apply (line_from_points a b) as AB
  euclid_apply (Elements.Book1.proposition_10 a b AB) as d
  euclid_apply (Elements.Book1.proposition_11 a b d AB) as c'
  euclid_apply (line_from_points d c') as CE
  -- Missed by Euclid: DC meets the circle at C and E, since D is inside it.
  euclid_apply (intersection_circle_line_2 d α CE)
  euclid_apply (intersections_circle_line α CE) as (c, e)
  euclid_apply (Elements.Book1.proposition_10 c e CE) as f
  use f
  -- a center G is on CE, and bisects it: it is F
  euclid_apply (proposition_1_corollary a b c' d o AB CE α)
  euclid_apply (point_on_circle_onlyif o c e α)
  euclid_apply (between_of_eq_dist c o e CE)
  euclid_assert o = f
  euclid_finish

end Elements.Book3
