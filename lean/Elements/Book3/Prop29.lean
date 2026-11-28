import SystemE
import Elements.Book1.Prop04
import Elements.Book3.Prop27

namespace Elements.Book3

/--
In equal circles, equal circumferences `BC`, `EF` (away from the centers `K`, `L`) are
subtended by equal straight lines.
-/
theorem proposition_29 : ∀ (b c e f k l : Point) (BC EF : Line) (α β : Circle),
  k.isCentre α ∧ l.isCentre β ∧ b.onCircle α ∧ c.onCircle α ∧ e.onCircle β ∧
  f.onCircle β ∧ |(k─b)| = |(l─e)| ∧ distinctPointsOnLine b c BC ∧
  distinctPointsOnLine e f EF ∧ ¬(k.onLine BC) ∧ ¬(l.onLine EF) ∧
  α.arc b c k = β.arc e f l → |(b─c)| = |(e─f)| :=
by
  euclid_intros
  -- the angles BKC, ELF are equal [Prop. 3.27]
  euclid_apply (proposition_27' b c e f k l BC EF α β)
  -- BK, KC are equal to EL, LF, and contain equal angles: BC = EF [Prop. 1.4]
  euclid_apply (line_from_points k b) as KB
  euclid_apply (line_from_points k c) as KC
  euclid_apply (line_from_points l e) as LE
  euclid_apply (line_from_points l f) as LF
  euclid_apply (point_on_circle_onlyif k b c α)
  euclid_apply (point_on_circle_onlyif l e f β)
  euclid_apply (Elements.Book1.proposition_4 k b c l e f KB BC KC LE EF LF)
  euclid_finish

end Elements.Book3
