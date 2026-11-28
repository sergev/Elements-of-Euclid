import SystemE
import Elements.Book1.Prop13
import Elements.Book1.Prop32
import Elements.Book3.Prop18
import Elements.Book3.Prop21
import Elements.Book3.Prop22
import Elements.Book3.Prop31

namespace Elements.Book3

/-
Prop. 3.32. `EF` touches the circle at `B`, and `BD` cuts it; `X` is in the segment on the
other side of `BD` from `F`, `Y` in the segment on the side of `F`.
-/

/-- Euclid's figure: `BA`, at right angles to `EF`, is a diameter, with `A` across `BD`
from `F`. -/
theorem proposition_32_lemma : ∀ (a b d e f o x y : Point) (BD EF : Line) (α : Circle),
  EF.touchesCircleAt α b ∧ e.onLine EF ∧ f.onLine EF ∧ between e b f ∧
  distinctPointsOnLine b d BD ∧ d.onCircle α ∧ o.isCentre α ∧ x.onCircle α ∧
  y.onCircle α ∧ x.opposingSides f BD ∧ y.sameSide f BD ∧ a.onCircle α ∧ between a o b ∧
  a.opposingSides f BD → ∠ d:b:f = ∠ b:x:d ∧ ∠ d:b:e = ∠ d:y:b :=
by
  euclid_intros
  -- the center is on BA, at right angles to EF [Prop. 3.19]: BA is a diameter
  euclid_apply (line_from_points a b) as BA
  euclid_apply (proposition_18 b f o EF α)
  euclid_apply (equal_angles b o a f f BA EF)
  -- ADB, in a semicircle, is right [Prop. 3.31]; BAD and ABD make a right angle
  -- [Prop. 1.32]
  euclid_apply (proposition_31 d a b o BA α)
  euclid_apply (line_from_points a d) as AD
  euclid_apply (extend_point BA b a) as z
  euclid_apply (Elements.Book1.proposition_32 d b a z BD BA AD)
  -- ABF is right, equal to BAD and ABD; take away ABD: DBF = BAD
  euclid_apply (sum_angles_onlyif b a f d BA EF)
  -- and BAD is the angle in the segment of X [Prop. 3.21]
  euclid_apply (proposition_21 x b d a o BD α)
  -- ABYD is a quadrilateral in a circle: BAD and BYD make two right angles [Prop. 3.22];
  -- and so do DBF and DBE [Prop. 1.13]. Missed by Euclid: the diagonals cut.
  euclid_apply (line_from_points a y) as AY
  euclid_apply (intersection_lines_opposing a y BD AY)
  euclid_apply (intersection_lines BD AY) as p
  euclid_apply (circle_points_between a y p α)
  euclid_apply (circle_line_intersections p b d BD α)
  euclid_apply (proposition_22_pair b a d y o BD AY α)
  euclid_apply (Elements.Book1.proposition_13 d b f e BD EF)
  euclid_finish

/--
The angles `DBF`, `DBE` the chord `BD` makes with the tangent `EF` are equal to the angles
in the alternate segments, at `X` and `Y`.
-/
theorem proposition_32 : ∀ (b d e f o x y : Point) (BD EF : Line) (α : Circle),
  EF.touchesCircleAt α b ∧ e.onLine EF ∧ f.onLine EF ∧ between e b f ∧
  distinctPointsOnLine b d BD ∧ d.onCircle α ∧ o.isCentre α ∧ x.onCircle α ∧
  y.onCircle α ∧ x.opposingSides f BD ∧ y.sameSide f BD →
  ∠ d:b:f = ∠ b:x:d ∧ ∠ d:b:e = ∠ d:y:b :=
by
  euclid_intros
  -- let BA be drawn at right angles to EF: through the center, a diameter
  euclid_apply (line_from_points b o) as BA
  euclid_apply (intersection_circle_line_extending_points α BA o b) as a
  -- Missed by Euclid: A may be on either side of BD, or at D.
  by_cases (a.onLine BD)
  · -- BD is a diameter: each angle is right [Props. 3.18, 3.31]
    euclid_assert a = d
    euclid_apply (proposition_18 b f o EF α)
    euclid_apply (proposition_18 b e o EF α)
    euclid_apply (equal_angles b o d f f BD EF)
    euclid_apply (equal_angles b o d e e BD EF)
    euclid_apply (proposition_31 x b d o BD α)
    euclid_apply (proposition_31 y b d o BD α)
    euclid_finish
  · by_cases (a.sameSide f BD)
    · -- the same, with E for F
      euclid_apply (proposition_32_lemma a b d f e o y x BD EF α)
      euclid_finish
    · euclid_apply (proposition_32_lemma a b d e f o x y BD EF α)
      euclid_finish

end Elements.Book3
