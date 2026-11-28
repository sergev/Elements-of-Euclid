import SystemE
import Elements.Book1.Prop04
import Elements.Book1.Prop06
import Elements.Book1.Prop17
import Elements.Book1.Prop23

namespace Elements.Book3

/--
To complete the circle of a given segment `ABC`: the chord `AC` is cut in half at `D`, and
`B` is on the circumference at right angles above `D`.
-/
theorem proposition_25 : ∀ (a b c d : Point) (AC : Line),
  distinctPointsOnLine a c AC ∧ between a d c ∧ |(a─d)| = |(d─c)| ∧ ¬(b.onLine AC) ∧
  ∠ a:d:b = ∟ → ∃ (e : Point) (α : Circle), e.isCentre α ∧ a.onCircle α ∧ b.onCircle α ∧
  c.onCircle α :=
by
  euclid_intros
  euclid_apply (line_from_points a b) as AB
  euclid_apply (line_from_points d b) as DB
  euclid_apply (line_from_points c b) as CB
  by_cases (∠ a:b:d = ∠ b:a:d)
  · -- Missed by Euclid: if ABD is equal to BAD, then DA = DB [Prop. 1.6], and D is the
    -- center
    euclid_apply (Elements.Book1.proposition_6 d a b AC AB DB)
    euclid_apply (circle_from_points d a) as α
    euclid_apply (point_on_circle_if d a b α)
    euclid_apply (point_on_circle_if d a c α)
    use d, α
  · -- the angle BAE equal to ABD [Prop. 1.23]; AE meets DB at E
    euclid_apply (Elements.Book1.proposition_23_side a b b a d d AB AB DB) as e'
    euclid_apply (line_from_points a e') as AE
    -- Missed by Euclid: AE meets DB, since ABD and BAE are less than two right angles
    -- [Prop. 1.17, Post. 5].
    euclid_apply (Elements.Book1.proposition_17 a d b AC DB AB)
    euclid_apply (lines_intersect e' a b d AE AB DB) as e
    euclid_apply (equal_angles a b b e' e AB AE)
    euclid_apply (equal_angles b a a d e AB DB)
    -- the angles ABE, BAE are equal, so EB = EA [Prop. 1.6]
    euclid_apply (Elements.Book1.proposition_6 e a b AE AB DB)
    -- Missed by Euclid: E is not D, ABD and BAD being unequal.
    euclid_assert e ≠ d
    euclid_assert ¬(e.onLine AC)
    -- AD = DC, DE common, and the angles at D right: AE = CE [Prop. 1.4]
    euclid_apply (line_from_points c e) as CE
    euclid_apply (right_angle_on_lines a d b a e AC DB)
    euclid_apply (right_angle_on_lines a d b c e AC DB)
    euclid_apply (Elements.Book1.proposition_4 d a e d c e AC AE DB AC CE DB)
    -- the circle with center E and radius EA goes through B and C [Prop. 3.9]
    euclid_apply (circle_from_points e a) as α
    euclid_apply (point_on_circle_if e a b α)
    euclid_apply (point_on_circle_if e a c α)
    use e, α

end Elements.Book3
