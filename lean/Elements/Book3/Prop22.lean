import SystemE
import Elements.Book1.Prop32
import Elements.Book3.Prop21

namespace Elements.Book3

/--
One pair of opposite angles of a quadrilateral `ABCD` in a circle, its diagonals `AC`
and `BD` cutting one another: `ABC` and `ADC` make two right angles.
-/
theorem proposition_22_pair : ∀ (a b c d f : Point) (AC BD : Line) (α : Circle),
  a.onCircle α ∧ b.onCircle α ∧ c.onCircle α ∧ d.onCircle α ∧ f.isCentre α ∧
  distinctPointsOnLine a c AC ∧ distinctPointsOnLine b d BD ∧
  a.opposingSides c BD ∧ b.opposingSides d AC → ∠ a:b:c + ∠ a:d:c = ∟ + ∟ :=
by
  euclid_intros
  euclid_apply (line_from_points a b) as AB
  euclid_apply (line_from_points b c) as BC
  -- Missed by Euclid: the diagonals cut at E, which places A, B, C, D.
  euclid_apply (intersection_lines_opposing a c BD AC)
  euclid_apply (intersection_lines BD AC) as e
  -- the three angles of ABC make two right angles [Prop. 1.32]
  euclid_apply (extend_point BC b c) as x
  euclid_apply (Elements.Book1.proposition_32 a b c x AB BC AC)
  -- CAB = BDC, in the segment BADC, and ACB = ADB, in the segment ADCB [Prop. 3.21]
  euclid_apply (proposition_21 a b c d f BC α)
  euclid_apply (proposition_21 c a b d f AB α)
  -- ADB and BDC make ADC
  euclid_apply (line_from_points d a) as DA
  euclid_apply (line_from_points d c) as DC
  euclid_apply (sum_angles_onlyif d a c b DA DC)
  euclid_finish

/-- The opposite angles of a quadrilateral `ABCD` in a circle make two right angles. -/
theorem proposition_22 : ∀ (a b c d f : Point) (AC BD : Line) (α : Circle),
  a.onCircle α ∧ b.onCircle α ∧ c.onCircle α ∧ d.onCircle α ∧ f.isCentre α ∧
  distinctPointsOnLine a c AC ∧ distinctPointsOnLine b d BD ∧
  a.opposingSides c BD ∧ b.opposingSides d AC →
  ∠ a:b:c + ∠ a:d:c = ∟ + ∟ ∧ ∠ b:a:d + ∠ b:c:d = ∟ + ∟ :=
by
  euclid_intros
  euclid_apply (proposition_22_pair a b c d f AC BD α)
  -- similarly for BAD and DCB
  euclid_apply (proposition_22_pair b a d c f BD AC α)
  euclid_finish

end Elements.Book3
