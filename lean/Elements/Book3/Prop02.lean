import SystemE
import Elements.Book1.Prop05
import Elements.Book1.Prop16
import Elements.Book1.Prop19

namespace Elements.Book3

/-- A chord `AB` falls inside the circle: each point `E` between `A` and `B` is inside. -/
theorem proposition_2 : ∀ (a b d e : Point) (α : Circle),
  a.onCircle α ∧ b.onCircle α ∧ d.isCentre α ∧ between a e b → e.insideCircle α :=
by
  euclid_intros
  euclid_apply (line_from_points a b) as AB
  euclid_apply (point_on_circle_onlyif d a b α)
  by_cases (d.onLine AB)
  · -- Missed by Euclid: when AB passes through the center D, DE < DA along the diameter.
    euclid_apply (between_of_eq_dist a d b AB)
    by_cases (e = d)
    · euclid_finish
    · by_cases (between a e d)
      · euclid_apply (between_if a e d)
        euclid_apply (point_in_circle_if d a e α)
        euclid_finish
      · euclid_apply (between_if b e d)
        euclid_apply (point_in_circle_if d b e α)
        euclid_finish
  · euclid_apply (line_from_points d a) as DA
    euclid_apply (line_from_points d b) as DB
    euclid_apply (line_from_points d e) as DE
    -- DA = DB, so the angles DAE, DBE are equal [Prop. 1.5]
    euclid_apply (Elements.Book1.proposition_5' d a b DA AB DB)
    -- the exterior angle DEB of triangle DAE is greater than DAE [Prop. 1.16]
    euclid_apply (Elements.Book1.proposition_16 d a e b DA AB DE)
    euclid_apply (equal_angles a d d e b DA AB)
    euclid_apply (equal_angles b d d a e DB AB)
    -- so DB, opposite the greater angle, is greater than DE [Prop. 1.19]
    euclid_apply (Elements.Book1.proposition_19 d e b DE AB DB)
    euclid_apply (point_in_circle_if d b e α)
    euclid_finish

end Elements.Book3
