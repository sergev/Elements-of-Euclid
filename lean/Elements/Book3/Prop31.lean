import SystemE
import Elements.Book1.Prop05
import Elements.Book1.Prop17
import Elements.Book1.Prop32
import Elements.Book3.Prop21
import Elements.Book3.Prop22

namespace Elements.Book3

/-
Prop. 3.31. Euclid's further claims, that the angle of the greater segment (between its
circumference and the chord) is greater than a right angle, and that of the lesser less,
are about angles contained by a curve, which System E does not have; they are left out,
as in Prop. 3.16.
-/

/-- The angle `BAC` in a semicircle, on the diameter `BC`, is right. -/
theorem proposition_31 : ∀ (a b c e : Point) (BC : Line) (α : Circle),
  a.onCircle α ∧ b.onCircle α ∧ c.onCircle α ∧ e.isCentre α ∧
  distinctPointsOnLine b c BC ∧ e.onLine BC ∧ ¬(a.onLine BC) → ∠ b:a:c = ∟ :=
by
  euclid_intros
  -- join AE, and draw BA through to F
  euclid_apply (circle_line_intersections e b c BC α)
  euclid_apply (line_from_points a e) as AE
  euclid_apply (line_from_points a b) as AB
  euclid_apply (line_from_points a c) as AC
  euclid_apply (extend_point AB b a) as f
  -- BE = EA and CE = EA: ABE = BAE, and ACE = CAE [Prop. 1.5]
  euclid_apply (point_on_circle_onlyif e a b α)
  euclid_apply (point_on_circle_onlyif e a c α)
  euclid_apply (Elements.Book1.proposition_5' e b a BC AB AE)
  euclid_apply (Elements.Book1.proposition_5' e c a BC AC AE)
  euclid_apply (equal_angles b e c a a BC AB)
  euclid_apply (equal_angles c e b a a BC AC)
  -- so BAC is equal to ABC and ACB together
  euclid_apply (sum_angles_onlyif a b c e AB AC)
  -- and FAC, external to ABC, is also equal to them [Prop. 1.32]
  euclid_apply (Elements.Book1.proposition_32 c b a f BC AB AC)
  -- so BAC = FAC, and each is right [Def. 1.10]
  euclid_apply (perpendicular_if b f a c AB)
  euclid_finish

/-- The angle `ABC` in a segment greater than a semicircle (the center `E` within it) is
less than a right angle. -/
theorem proposition_31' : ∀ (a b c e : Point) (AC : Line) (α : Circle),
  a.onCircle α ∧ b.onCircle α ∧ c.onCircle α ∧ e.isCentre α ∧
  distinctPointsOnLine a c AC ∧ e.sameSide b AC → ∠ a:b:c < ∟ :=
by
  euclid_intros
  -- in Euclid's figure BC is a diameter; let B' be the end of the diameter through C,
  -- in the same segment as B [Prop. 3.21]
  euclid_apply (line_from_points c e) as CE
  euclid_apply (intersection_circle_line_extending_points α CE e c) as b'
  euclid_apply (proposition_21 b a c b' e AC α)
  -- the angle B'AC in the semicircle is right, so AB'C is less than a right angle
  -- [Prop. 1.17]
  euclid_apply (proposition_31 a b' c e CE α)
  euclid_apply (line_from_points a b') as AB
  euclid_apply (Elements.Book1.proposition_17 c a b' AC AB CE)
  euclid_finish

/-- The angle `ADC` in a segment less than a semicircle is greater than a right angle. -/
theorem proposition_31'' : ∀ (a c d e : Point) (AC : Line) (α : Circle),
  a.onCircle α ∧ c.onCircle α ∧ d.onCircle α ∧ e.isCentre α ∧
  distinctPointsOnLine a c AC ∧ e.opposingSides d AC → ∠ a:d:c > ∟ :=
by
  euclid_intros
  euclid_apply (line_from_points c e) as CE
  euclid_apply (intersection_circle_line_extending_points α CE e c) as b
  euclid_apply (proposition_31' a b c e AC α)
  -- ABCD is a quadrilateral in a circle: ABC and ADC make two right angles [Prop. 3.22].
  -- Missed by Euclid: its diagonals cut one another, at P inside the circle.
  euclid_apply (line_from_points b d) as BD
  euclid_apply (intersection_lines_opposing b d AC BD)
  euclid_apply (intersection_lines AC BD) as p
  euclid_apply (circle_points_between b d p α)
  euclid_apply (circle_line_intersections p a c AC α)
  euclid_apply (proposition_22_pair a b c d e AC BD α)
  euclid_finish

end Elements.Book3
