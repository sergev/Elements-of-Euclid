import SystemE

/-
Book 3's circumferences (arcs). System E has no arcs; Euclid compares circumferences as
magnitudes in Props. 3.26–3.30. `α.arc b c s` is the size of the circumference of `α`
from `b` to `c` on the side of the line `bc` away from `s`: an angle `bsc` with `s` on
the circle, or at the center `s`, stands upon it (Def. 3.9). `α.circumference` is the
whole circle. The axioms are what Euclid assumes of them.
-/

namespace Circle

/-- The circumference of `α` from `b` to `c`, away from `s`. -/
opaque arc : Circle → Point → Point → Point → ℝ

/-- The whole circumference of `α`. -/
opaque circumference : Circle → ℝ

end Circle

namespace Elements.Book3

/-- A circumference is the same from either end. -/
axiom arc_symm : ∀ (b c s : Point) (α : Circle), α.arc b c s = α.arc c b s

/-- It depends only on the side of `bc` away from which it lies. -/
axiom arc_side : ∀ (b c s s' : Point) (L : Line) (α : Circle),
  b.onCircle α ∧ c.onCircle α ∧ distinctPointsOnLine b c L ∧ s.sameSide s' L →
  α.arc b c s = α.arc b c s'

/-- A circumference is a magnitude. -/
axiom arc_pos : ∀ (b c s : Point) (L : Line) (α : Circle),
  b.onCircle α ∧ c.onCircle α ∧ distinctPointsOnLine b c L ∧ ¬(s.onLine L) →
  0 < α.arc b c s

/-- The circumferences on either side of `bc` make the whole circle. -/
axiom arc_whole : ∀ (b c s s' : Point) (L : Line) (α : Circle),
  b.onCircle α ∧ c.onCircle α ∧ distinctPointsOnLine b c L ∧ s.opposingSides s' L →
  α.arc b c s + α.arc b c s' = α.circumference

/-- A point `k` on the circumference `bc` away from `s` divides it (C.N. 2). -/
axiom arc_add : ∀ (b c k s : Point) (L : Line) (α : Circle),
  b.onCircle α ∧ c.onCircle α ∧ k.onCircle α ∧ distinctPointsOnLine b c L ∧
  k.opposingSides s L → α.arc b c s = α.arc b k c + α.arc k c b

/-- Equal circles have equal circumferences (C.N. 4). -/
axiom circumference_eq : ∀ (g p h q : Point) (α β : Circle),
  g.isCentre α ∧ p.onCircle α ∧ h.isCentre β ∧ q.onCircle β ∧ |(g─p)| = |(h─q)| →
  α.circumference = β.circumference

/--
Equal segments have equal circumferences (C.N. 4): in equal circles, the segments on
equal chords `bc`, `ef` admitting equal angles at `x`, `y` coincide when applied
(Prop. 3.24), and so do their circumferences, away from `x'`, `y'` across the chords.
-/
axiom arc_eq_of_segments :
  ∀ (b c e f g h x y x' y' : Point) (BC EF : Line) (α β : Circle),
  g.isCentre α ∧ h.isCentre β ∧ b.onCircle α ∧ c.onCircle α ∧ e.onCircle β ∧
  f.onCircle β ∧ |(g─b)| = |(h─e)| ∧ distinctPointsOnLine b c BC ∧
  distinctPointsOnLine e f EF ∧ |(b─c)| = |(e─f)| ∧ x.onCircle α ∧ y.onCircle β ∧
  ∠ b:x:c = ∠ e:y:f ∧ x.opposingSides x' BC ∧
  y.opposingSides y' EF → α.arc b c x' = β.arc e f y'

end Elements.Book3
