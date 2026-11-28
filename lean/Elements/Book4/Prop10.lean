import SystemE
import Elements.Book1.Prop05
import Elements.Book1.Prop06
import Elements.Book1.Prop32
import Elements.Book2.Prop11
import Elements.Book3.Prop32
import Elements.Book3.Prop37
import Elements.Book4.Lemmas
import Elements.Book4.Prop01
import Elements.Book4.Prop05

namespace Elements.Book4

/--
The figure of Prop. 4.10: `AB` cut at `C` so that the rectangle `AB`, `BC` is equal to the
square on `CA` [Prop. 2.11]; `BD`, equal to `AC`, inserted into the circle with center `A`
and radius `AB` [Prop. 4.1].
-/
theorem proposition_10_figure : ∀ (a b : Point) (AB : Line),
  distinctPointsOnLine a b AB →
  ∃ (c d : Point), between a c b ∧ |(a─b)| * |(b─c)| = |(a─c)| * |(a─c)| ∧
  |(a─d)| = |(a─b)| ∧ |(b─d)| = |(a─c)| ∧ ¬(d.onLine AB) :=
by
  euclid_intros
  euclid_apply (Elements.Book2.proposition_11 a b AB) as c
  euclid_apply (circle_from_points a b) as BDE
  euclid_apply (between_if a c b)
  euclid_apply (proposition_1 a b a c BDE) as d
  euclid_apply (point_on_circle_onlyif a b d BDE)
  -- Missed by Euclid: D is off AB, BD being neither nothing nor the diameter.
  have : ¬(d.onLine AB) := by
    intro
    by_cases (between d a b)
    · have := between_if d a b ‹_›
      have := segment_symmetric d a
      have := segment_symmetric d b
      euclid_assert |(a─c)| < |(a─b)|
      have := segment_gte_zero (a─b)
      linarith
    · euclid_apply (eq_of_same_ray d b a AB)
      euclid_apply (zero_segment_onlyif b d)
      euclid_finish
  use c, d

/-- To construct an isosceles triangle `ABD` having each of the angles at the base `BD`
double the remaining angle. -/
theorem proposition_10 : ∀ (a b : Point) (AB : Line),
  distinctPointsOnLine a b AB →
  ∃ (d : Point) (BD DA : Line), formTriangle a b d AB BD DA ∧ |(a─b)| = |(a─d)| ∧
  ∠ a:b:d = ∠ b:a:d + ∠ b:a:d ∧ ∠ a:d:b = ∠ b:a:d + ∠ b:a:d :=
by
  euclid_intros
  euclid_apply (proposition_10_figure a b AB) as (c, d)
  -- let AD, DC be joined, and the circle ACD circumscribed about the triangle ACD
  -- [Prop. 4.5]
  euclid_apply (line_from_points a d) as DA
  euclid_apply (line_from_points d c) as DC
  euclid_apply (line_from_points b d) as BD
  euclid_apply (proposition_5 a c d AB DC DA) as (f, ACD)
  -- AB by BC is equal to the square on AC, that is on BD: BD touches the circle ACD
  -- [Prop. 3.37]
  euclid_apply (Elements.Book3.proposition_37 a d c b f AB BD ACD)
  -- DC is drawn across from the point of contact D: BDC is equal to the angle DAC in
  -- the alternate segment [Prop. 3.32]
  -- Missed by Euclid: the segment on B's side of DC has a point Y.
  euclid_apply (extend_point BD b d) as e
  euclid_apply (points_on_both_sides d c b DC ACD) as (x, y)
  euclid_apply (Elements.Book3.proposition_32 d c e b f a y DC BD ACD)
  -- add CDA to both: BDA is equal to CDA and DAC, that is to the exterior angle BCD
  -- [Prop. 1.32]
  euclid_apply (sum_angles_onlyif d b a c BD DA)
  euclid_apply (Elements.Book1.proposition_32 d a c b DA AB DC)
  -- BDA is equal to DBA, since AD = AB [Prop. 1.5]
  euclid_apply (Elements.Book1.proposition_5' a b d AB BD DA)
  -- DBC is equal to BCD: BD = DC [Prop. 1.6]; so CA = CD, and CDA = DAC [Prop. 1.5]
  euclid_apply (equal_angles b a c d d AB BD)
  euclid_apply (Elements.Book1.proposition_6 d b c BD AB DC)
  euclid_apply (Elements.Book1.proposition_5' c d a DC DA AB)
  -- BCD, equal to CDA and DAC, is double CAD; and BDA, DBA are equal to BCD
  euclid_apply (equal_angles a c b d d AB DA)
  use d, BD, DA
  euclid_finish

end Elements.Book4
