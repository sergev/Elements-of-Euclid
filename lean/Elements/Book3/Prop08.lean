import SystemE
import Elements.Book1.Prop04
import Elements.Book1.Prop20
import Elements.Book1.Prop23
import Elements.Book1.Prop24

namespace Elements.Book3

/-
Prop. 3.8. `D` is a point outside a circle with center `M`, and the line `DA` through the
center meets the circle at `G` and `A`, `G` nearer. Of the straight lines from `D` to the
circle, `DA` is the greatest and `DG` the least (`proposition_8`); one nearer to `DA`, by
the angle at `M`, is greater, on the concave and on the convex circumference
(`proposition_8_nearer`); and only two equal lines fall from `D`, one on each side of `DG`
(`proposition_8_equal`, `proposition_8_only`).

Euclid proves the convex case of "nearer" by Prop. 1.21, with the point inside the
triangle read off the figure; Prop. 1.24, which he uses for the concave case, gives both.
-/

/-- `DA` is the greatest, and `DG` the least, of the lines from `D` to the circle. -/
theorem proposition_8 : ∀ (a d e g m : Point) (AD : Line) (α : Circle),
  a.onLine AD ∧ g.onLine AD ∧ a.onCircle α ∧ g.onCircle α ∧ e.onCircle α ∧ m.isCentre α ∧
  between d g m ∧ between g m a ∧ e ≠ a ∧ e ≠ g →
  |(d─e)| < |(d─a)| ∧ |(d─g)| < |(d─e)| :=
by
  euclid_intros
  euclid_apply (line_from_points m e) as ME
  euclid_apply (line_from_points d e) as DE
  euclid_apply (point_on_circle_onlyif m a e α)
  euclid_apply (point_on_circle_onlyif m g e α)
  -- AD = EM + MD, greater than ED [Prop. 1.20]
  euclid_apply (Elements.Book1.proposition_20 m e d ME DE AD)
  euclid_apply (between_if g m a)
  euclid_apply (between_if d m a)
  -- MK and KD are greater than MD, and MG = MK: KD is greater than GD [Prop. 1.20]
  euclid_apply (Elements.Book1.proposition_20 e m d ME AD DE)
  euclid_apply (between_if d g m)
  euclid_finish

/-- Of two lines `DE`, `DF`, the one nearer to `DA` (by the angle at `M`) is greater. -/
theorem proposition_8_nearer : ∀ (a d e f g m : Point) (AD : Line) (α : Circle),
  a.onLine AD ∧ g.onLine AD ∧ a.onCircle α ∧ g.onCircle α ∧ e.onCircle α ∧ f.onCircle α ∧
  m.isCentre α ∧ between d g m ∧ between g m a ∧ ¬(e.onLine AD) ∧ ¬(f.onLine AD) ∧
  ∠ f:m:d < ∠ e:m:d → |(d─f)| < |(d─e)| :=
by
  euclid_intros
  euclid_apply (line_from_points m e) as ME
  euclid_apply (line_from_points d e) as DE
  euclid_apply (line_from_points m f) as MF
  euclid_apply (line_from_points d f) as DF
  -- ME = MF, MD common, and the angle EMD greater than FMD [Prop. 1.24]
  euclid_apply (point_on_circle_onlyif m e f α)
  euclid_apply (Elements.Book1.proposition_24 m e d m f d ME DE AD MF DF AD)
  euclid_finish

/-- A line `DB` equal to `DK` falls on the other side of `DG`. -/
theorem proposition_8_equal : ∀ (a d g k m : Point) (AD : Line) (α : Circle),
  a.onLine AD ∧ g.onLine AD ∧ a.onCircle α ∧ g.onCircle α ∧ k.onCircle α ∧ m.isCentre α ∧
  between d g m ∧ between g m a ∧ ¬(k.onLine AD) →
  ∃ b : Point, b.onCircle α ∧ b.opposingSides k AD ∧ |(d─b)| = |(d─k)| :=
by
  euclid_intros
  euclid_apply (line_from_points m k) as MK
  euclid_apply (line_from_points d k) as DK
  -- the angle DMB equal to KMD, on the other side [Prop. 1.23]
  euclid_apply (exists_point_opposite AD k) as x
  euclid_apply (Elements.Book1.proposition_23_side m d m k d x AD MK AD) as b'
  euclid_apply (line_from_points m b') as MB
  euclid_apply (extend_point MB b' m) as b''
  euclid_apply (intersection_circle_line_extending_points α MB m b'') as b
  euclid_apply (equal_angles m d d b' b AD MB)
  euclid_apply (line_from_points d b) as DB
  -- MK = MB, MD common, and the angles at M equal: DK = DB [Prop. 1.4]
  euclid_apply (point_on_circle_onlyif m k b α)
  euclid_apply (Elements.Book1.proposition_4 m k d m b d MK DK AD MB DB AD)
  use b
  euclid_finish

/-- On one side of `AD`, a line `DN` equal to `DK` is `DK`. -/
theorem proposition_8_side : ∀ (a d g k m n : Point) (AD : Line) (α : Circle),
  a.onLine AD ∧ g.onLine AD ∧ a.onCircle α ∧ g.onCircle α ∧ k.onCircle α ∧ n.onCircle α ∧
  m.isCentre α ∧ between d g m ∧ between g m a ∧ k.sameSide n AD ∧
  |(d─n)| = |(d─k)| → n = k :=
by
  euclid_intros
  -- otherwise the nearer to DG would equal the further
  rcases lt_trichotomy (∠ n:m:d) (∠ k:m:d) with _ | _ | _
  · euclid_apply (proposition_8_nearer a d k n g m AD α)
    exfalso
    euclid_finish
  · -- Missed by Euclid: with equal angles at M, N is on MK, and MN = MK.
    euclid_apply (line_from_points m k) as MK
    euclid_apply (on_line_of_eq_angle n MK m k d AD)
    euclid_apply (point_on_circle_onlyif m k n α)
    euclid_apply (eq_of_same_ray n k m MK)
    euclid_finish
  · euclid_apply (proposition_8_nearer a d n k g m AD α)
    exfalso
    euclid_finish

/-- No other line from `D` is equal to `DK`. -/
theorem proposition_8_only : ∀ (a b d g k m n : Point) (AD : Line) (α : Circle),
  a.onLine AD ∧ g.onLine AD ∧ a.onCircle α ∧ g.onCircle α ∧ k.onCircle α ∧ b.onCircle α ∧
  n.onCircle α ∧ m.isCentre α ∧ between d g m ∧ between g m a ∧ k.opposingSides b AD ∧
  |(d─b)| = |(d─k)| ∧ |(d─n)| = |(d─k)| → n = k ∨ n = b :=
by
  euclid_intros
  -- Missed by Euclid: DN is neither DA nor DG, so N is off AD, on the side of K or of B.
  euclid_apply (proposition_8 a d k g m AD α)
  by_cases (n.onLine AD)
  · by_cases (n = a)
    · exfalso
      euclid_finish
    · euclid_assert n = g
      exfalso
      euclid_finish
  · by_cases (k.sameSide n AD)
    · euclid_apply (proposition_8_side a d g k m n AD α)
      euclid_finish
    · euclid_apply (proposition_8_side a d g b m n AD α)
      euclid_finish

end Elements.Book3
