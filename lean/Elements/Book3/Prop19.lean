import SystemE
import Elements.Book1.Prop23
import Elements.Book3.Prop18

namespace Elements.Book3

/-- A perpendicular `CA` to a tangent at the point of contact goes through the center. -/
theorem proposition_19 : ∀ (a c d f : Point) (DE CA : Line) (α : Circle),
  DE.touchesCircleAt α c ∧ d.onLine DE ∧ d ≠ c ∧ c.onLine CA ∧ a.onLine CA ∧ a ≠ c ∧
  ∠ d:c:a = ∟ ∧ f.isCentre α → f.onLine CA :=
by
  euclid_intros
  -- if not, let F be the center, and join CF: the angle FCD is right [Prop. 3.18], and
  -- so is ACD, the lesser equal to the greater
  euclid_apply (proposition_18 c d f DE α)
  -- Missed by Euclid: A is off DE, the angle DCA being right.
  euclid_apply (angle_symm d c a)
  have : (0 : ℝ) < ∠ a:c:d := by linarith [Elements.Book1.right_angle_pos]
  euclid_apply (Elements.Book1.not_on_line_of_angle a c d CA DE)
  by_cases (f.sameSide a DE)
  · euclid_apply (on_line_of_eq_angle f CA c a d DE)
    euclid_finish
  · -- Missed by Euclid: F may be on the other side of DE, with the continuation of AC.
    euclid_apply (extend_point CA a c) as a'
    euclid_apply (right_angle_on_lines d c a d a' DE CA)
    euclid_apply (on_line_of_eq_angle f CA c a' d DE)
    euclid_finish

end Elements.Book3
