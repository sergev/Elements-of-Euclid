import SystemE
import Elements.Book1.Prop03
import Elements.Book1.Prop11
import Elements.Book1.Prop20
import Elements.Book1.Prop47
import Elements.Book3.Lemmas
import Elements.Book3.Prop14

namespace Elements.Book3

/-- A diameter `AD` is greater than a chord `BC` not through the center. -/
theorem proposition_15 : ∀ (a b c d e : Point) (BC : Line) (α : Circle),
  a.onCircle α ∧ d.onCircle α ∧ b.onCircle α ∧ c.onCircle α ∧ e.isCentre α ∧
  between a e d ∧ distinctPointsOnLine b c BC ∧ ¬(e.onLine BC) → |(b─c)| < |(a─d)| :=
by
  euclid_intros
  -- AD is equal to BE and EC, which are greater than BC [Prop. 1.20]. (Euclid argues
  -- with MN, equal to BC [Prop. 3.14]; BC itself serves.)
  euclid_apply (line_from_points e b) as EB
  euclid_apply (line_from_points e c) as EC
  euclid_apply (Elements.Book1.proposition_20 e b c EB BC EC)
  euclid_apply (point_on_circle_onlyif e a b α)
  euclid_apply (point_on_circle_onlyif e d c α)
  euclid_apply (between_if a e d)
  euclid_finish

/--
Of two chords `BC`, `FG` with perpendiculars `EH`, `EK` from the center, the nearer
to the center (`EH` less than `EK`, Def. 3.5) is the greater.
-/
theorem proposition_15' : ∀ (b c e f g h k : Point) (BC FG : Line) (α : Circle),
  distinctPointsOnLine b c BC ∧ distinctPointsOnLine f g FG ∧
  b.onCircle α ∧ c.onCircle α ∧ f.onCircle α ∧ g.onCircle α ∧ e.isCentre α ∧
  ¬(e.onLine BC) ∧ ¬(e.onLine FG) ∧ h.onLine BC ∧ h ≠ b ∧ ∠ b:h:e = ∟ ∧
  k.onLine FG ∧ k ≠ f ∧ ∠ f:k:e = ∟ ∧ |(e─h)| < |(e─k)| → |(f─g)| < |(b─c)| :=
by
  euclid_intros
  euclid_apply (proposition_3_foot b c e h BC α)
  euclid_apply (proposition_3_foot f g e k FG α)
  -- EL equal to EH [Prop. 1.3], and MN through L at right angles to EK [Prop. 1.11]
  euclid_apply (line_from_points e k) as EK
  euclid_apply (line_from_points e h) as EH
  euclid_apply (Elements.Book1.proposition_3 e k e h EK EH) as l
  euclid_apply (Elements.Book1.proposition_11 e k l EK) as x
  euclid_apply (line_from_points l x) as MN
  -- Missed by Euclid: L is inside the circle, so MN meets it at M and N.
  euclid_apply (circle_points_between b c h α)
  euclid_apply (point_in_circle_onlyif e b h α)
  euclid_apply (point_in_circle_if e b l α)
  euclid_apply (intersection_circle_line_2 l α MN)
  euclid_apply (intersections_circle_line α MN) as (m, n)
  euclid_apply (right_angle_on_lines e l x e m EK MN)
  euclid_apply (right_angle_on_lines e l x k m EK MN)
  euclid_apply (angle_symm m l e)
  -- EL = EH, so MN = BC [Prop. 3.14]
  euclid_apply (proposition_14' m n b c e l h MN BC α)
  -- Euclid has the angle MEN greater than FEG from the figure, so MN greater than FG
  -- [Prop. 1.24]. Missed by Euclid: from the squares, as in 3.14 [Prop. 1.47], ML is
  -- greater than FK.
  euclid_apply (proposition_3_foot m n e l MN α)
  euclid_apply (line_from_points e m) as EM
  euclid_apply (line_from_points e f) as EF
  euclid_apply (Elements.Book1.proposition_47 l m e MN EM EK)
  euclid_apply (Elements.Book1.proposition_47 k f e FG EF EK)
  euclid_apply (point_on_circle_onlyif e m f α)
  euclid_assert |(m─e)| = |(f─e)|
  euclid_apply (square_lt_of_lt l e k e)
  euclid_assert |(f─k)| * |(f─k)| < |(m─l)| * |(m─l)|
  euclid_apply (lt_of_square_lt f k m l)
  euclid_apply (between_if m l n)
  euclid_apply (between_if f k g)
  euclid_finish

end Elements.Book3
