import SystemE
import Elements.Book1.Prop08
import Elements.Book3.Prop26

namespace Elements.Book3

/--
In equal circles, equal chords `AB`, `DE`, not through the centers `K`, `L`, cut off
equal lesser circumferences (away from the centers).
-/
theorem proposition_28 : ∀ (a b d e k l : Point) (AB DE : Line) (α β : Circle),
  k.isCentre α ∧ l.isCentre β ∧ a.onCircle α ∧ b.onCircle α ∧ d.onCircle β ∧
  e.onCircle β ∧ |(k─a)| = |(l─d)| ∧ distinctPointsOnLine a b AB ∧
  distinctPointsOnLine d e DE ∧ ¬(k.onLine AB) ∧ ¬(l.onLine DE) ∧
  |(a─b)| = |(d─e)| → α.arc a b k = β.arc d e l :=
by
  euclid_intros
  -- AK, KB are equal to DL, LE, and the bases AB, DE: the angles AKB, DLE are equal
  -- [Prop. 1.8]
  euclid_apply (line_from_points k a) as KA
  euclid_apply (line_from_points k b) as KB
  euclid_apply (line_from_points l d) as LD
  euclid_apply (line_from_points l e) as LE
  euclid_apply (point_on_circle_onlyif k a b α)
  euclid_apply (point_on_circle_onlyif l d e β)
  euclid_apply (Elements.Book1.proposition_8 k a b l d e KA AB KB LD DE LE)
  -- equal angles at the centers stand on equal circumferences [Prop. 3.26]
  euclid_apply (proposition_26' a b d e k l AB DE α β)
  euclid_finish

/-- And equal greater circumferences (away from `C`, `F` across the chords). -/
theorem proposition_28' : ∀ (a b c d e f k l : Point) (AB DE : Line) (α β : Circle),
  k.isCentre α ∧ l.isCentre β ∧ a.onCircle α ∧ b.onCircle α ∧ d.onCircle β ∧
  e.onCircle β ∧ |(k─a)| = |(l─d)| ∧ distinctPointsOnLine a b AB ∧
  distinctPointsOnLine d e DE ∧ ¬(k.onLine AB) ∧ ¬(l.onLine DE) ∧ |(a─b)| = |(d─e)| ∧
  c.opposingSides k AB ∧ f.opposingSides l DE → α.arc a b c = β.arc d e f :=
by
  euclid_intros
  euclid_apply (proposition_28 a b d e k l AB DE α β)
  -- the whole circles are equal: the remaining circumferences are equal
  euclid_apply (circumference_eq k a l d α β)
  euclid_apply (arc_whole a b k c AB α)
  euclid_apply (arc_whole d e l f DE β)
  euclid_finish

end Elements.Book3
