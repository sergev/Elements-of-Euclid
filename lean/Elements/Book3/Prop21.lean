import SystemE
import Elements.Book3.Prop20

namespace Elements.Book3

/-- Angles `BAD`, `BED` in the same segment are equal. -/
theorem proposition_21 : ∀ (a b d e f : Point) (BD : Line) (α : Circle),
  a.onSegment α b d BD e ∧ e.onCircle α ∧ f.isCentre α → ∠ b:a:d = ∠ b:e:d :=
by
  euclid_intros
  -- with the center F, the angle BFD is double BAD and double BED [Prop. 3.20]
  by_cases (f.sameSide a BD)
  · euclid_apply (proposition_20 a b d f BD α)
    euclid_apply (proposition_20 e b d f BD α)
    euclid_finish
  · -- Missed by Euclid: the segment may be a semicircle, or less.
    by_cases (f.onLine BD)
    · euclid_apply (proposition_20'' a b d f BD α)
      euclid_apply (proposition_20'' e b d f BD α)
      euclid_finish
    · euclid_apply (proposition_20' a b d f BD α)
      euclid_apply (proposition_20' e b d f BD α)
      euclid_finish

end Elements.Book3
