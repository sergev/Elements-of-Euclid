import SystemE
import Elements.Book1.Prop04
import Elements.Book1.Prop10
import Elements.Book1.Prop11
import Elements.Book3.Prop01
import Elements.Book3.Prop28

namespace Elements.Book3

/--
To cut a given circumference `ADB` in half (`D'` on it): `D` divides it into the
circumferences `AD` and `DB`, away from `B` and `A`.
-/
theorem proposition_30 : ∀ (a b d' o : Point) (AB : Line) (α : Circle),
  a.onCircle α ∧ b.onCircle α ∧ distinctPointsOnLine a b AB ∧ d'.onCircle α ∧
  ¬(d'.onLine AB) ∧ o.isCentre α →
  ∃ d : Point, d.onCircle α ∧ d.sameSide d' AB ∧ α.arc a d b = α.arc d b a :=
by
  euclid_intros
  -- cut AB in half at C [Prop. 1.10], and draw CD at right angles to AB [Prop. 1.11]
  euclid_apply (Elements.Book1.proposition_10 a b AB) as c
  euclid_apply (Elements.Book1.proposition_11' a b c d' AB) as p
  euclid_apply (line_from_points c p) as CD
  euclid_apply (extend_point CD p c) as q
  euclid_apply (circle_points_between a b c α)
  euclid_apply (intersection_circle_line_extending_points α CD c q) as d
  -- AC = CB, CD common, and the angles at C right: AD = DB [Prop. 1.4]
  euclid_apply (line_from_points a d) as AD
  euclid_apply (line_from_points d b) as DB
  euclid_apply (right_angle_on_lines a c p a d AB CD)
  euclid_apply (right_angle_on_lines a c p b d AB CD)
  euclid_apply (Elements.Book1.proposition_4 c a d c b d AB AD CD AB DB CD)
  -- equal straight lines cut off equal circumferences [Prop. 3.28]; AD and DB are each
  -- less than a semicircle. Missed by Euclid: the center O is on CD [Prop. 3.1
  -- corollary], on the side of C from D, so the circumferences AD, DB are away from O.
  euclid_apply (proposition_1_corollary a b p c o AB CD α)
  euclid_assert ¬(between o d c)
  euclid_apply (proposition_28 a d d b o o AD DB α α)
  euclid_apply (arc_side a d o b AD α)
  euclid_apply (arc_side d b o a DB α)
  use d
  euclid_finish

end Elements.Book3
