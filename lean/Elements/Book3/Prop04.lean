import SystemE
import Elements.Book3.Prop03

namespace Elements.Book3

/--
Two chords `AC`, `BD` cutting at `E`, neither through the center, do not bisect
each other.
-/
theorem proposition_4 : ∀ (a b c d e f : Point) (AC BD : Line) (α : Circle),
  distinctPointsOnLine a c AC ∧ distinctPointsOnLine b d BD ∧ AC ≠ BD ∧
  a.onCircle α ∧ b.onCircle α ∧ c.onCircle α ∧ d.onCircle α ∧
  between a e c ∧ between b e d ∧ f.isCentre α ∧ ¬(f.onLine AC) ∧ ¬(f.onLine BD) →
  ¬(|(a─e)| = |(e─c)| ∧ |(b─e)| = |(e─d)|) :=
by
  euclid_intros
  euclid_apply (line_from_points f e) as FE
  -- FE, through the center, cuts AC and BD in half, so at right angles [Prop. 3.3]
  euclid_apply (proposition_3 a c f e AC α)
  euclid_apply (proposition_3 b d f e BD α)
  -- FEA = FEB, the lesser to the greater: B is on AC
  by_cases (b.sameSide a FE)
  · euclid_apply (on_line_of_eq_angle b AC e a f FE)
    euclid_finish
  · euclid_apply (right_angle_on_lines a e f c f AC FE)
    euclid_apply (on_line_of_eq_angle b AC e c f FE)
    euclid_finish

end Elements.Book3
