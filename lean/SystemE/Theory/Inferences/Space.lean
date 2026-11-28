import SystemE.Theory.Sorts.Space
import SystemE.Theory.Inferences

/-!
Inference rules of space, in System E's form, so that saturation uses them: incidence
(Hilbert I.1–I.8), separation by a plane, every plane a copy of System E's plane
(`Plane.over`), and the measures, with the volume of a tetrahedron. Each is true in ℝ³.
-/

namespace Space

/-! Incidence -/

/-- I.2: two points determine a line. -/
axiom line_unique : ∀ (a b : Point) (L M : Line),
  a ≠ b ∧ a.onLine L ∧ b.onLine L ∧ a.onLine M ∧ b.onLine M → L = M

/-- I.5: three points not on a line determine a plane. -/
axiom plane_unique : ∀ (a b c : Point) (L : Line) (π σ : Plane),
  a ≠ b ∧ a.onLine L ∧ b.onLine L ∧ ¬ c.onLine L ∧ a.onPlane π ∧ b.onPlane π ∧
  c.onPlane π ∧ a.onPlane σ ∧ b.onPlane σ ∧ c.onPlane σ → π = σ

/-- I.6: a line with two points on a plane is in it. -/
axiom line_in_plane : ∀ (a b : Point) (L : Line) (π : Plane),
  a ≠ b ∧ a.onLine L ∧ b.onLine L ∧ a.onPlane π ∧ b.onPlane π → L.inPlane π

axiom on_plane_of_in_plane : ∀ (a : Point) (L : Line) (π : Plane),
  a.onLine L ∧ L.inPlane π → a.onPlane π

/-! Betweenness -/

axiom between_symm : ∀ (a b c : Point), between a b c →
  between c b a ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ¬ between b a c

axiom between_on_line_1 : ∀ (a b c : Point) (L : Line),
  between a b c ∧ a.onLine L ∧ c.onLine L → b.onLine L

axiom between_on_line_2 : ∀ (a b c : Point) (L : Line),
  between a b c ∧ a.onLine L ∧ b.onLine L → c.onLine L

axiom between_on_plane : ∀ (a b c : Point) (π : Plane),
  between a b c ∧ a.onPlane π ∧ c.onPlane π → b.onPlane π

/-! Separation by a plane -/

axiom same_side_not_on : ∀ (a b : Point) (π : Plane),
  a.sameSide b π → ¬ a.onPlane π ∧ ¬ b.onPlane π

axiom same_side_refl : ∀ (a : Point) (π : Plane), ¬ a.onPlane π → a.sameSide a π

axiom same_side_symm : ∀ (a b : Point) (π : Plane), a.sameSide b π → b.sameSide a π

axiom same_side_trans : ∀ (a b c : Point) (π : Plane),
  a.sameSide b π ∧ b.sameSide c π → a.sameSide c π

/-- A plane has two sides. -/
axiom same_side_two : ∀ (a b c : Point) (π : Plane),
  ¬ a.onPlane π ∧ ¬ b.onPlane π ∧ ¬ c.onPlane π ∧ ¬ a.sameSide b π ∧
  ¬ b.sameSide c π → a.sameSide c π

/-- A segment through the plane joins opposite sides. -/
axiom between_opposite : ∀ (a b c : Point) (π : Plane),
  between a b c ∧ b.onPlane π ∧ ¬ a.onPlane π → ¬ a.sameSide c π

axiom between_same_side : ∀ (a b c : Point) (π : Plane),
  between a b c ∧ a.sameSide c π → a.sameSide b π

/-- A ray from a point of the plane stays on one side. -/
axiom ray_same_side : ∀ (a b c : Point) (π : Plane),
  between a b c ∧ a.onPlane π ∧ ¬ c.onPlane π → b.sameSide c π

/-! Every plane carries System E's plane -/

axiom over_on_plane : ∀ (π : Plane) (a' : _root_.Point) (a : Point),
  π.over a' a → a.onPlane π

axiom over_unique : ∀ (π : Plane) (a' : _root_.Point) (a b : Point),
  π.over a' a ∧ π.over a' b → a = b

axiom over_inj : ∀ (π : Plane) (a' b' : _root_.Point) (a : Point),
  π.over a' a ∧ π.over b' a → a' = b'

axiom over_line_in_plane : ∀ (π : Plane) (L' : _root_.Line) (L : Line),
  π.overLine L' L → L.inPlane π

axiom over_line_unique : ∀ (π : Plane) (L' : _root_.Line) (L M : Line),
  π.overLine L' L ∧ π.overLine L' M → L = M

axiom over_line_inj : ∀ (π : Plane) (L' M' : _root_.Line) (L : Line),
  π.overLine L' L ∧ π.overLine M' L → L' = M'

axiom over_on_line : ∀ (π : Plane) (a' : _root_.Point) (L' : _root_.Line) (a : Point)
  (L : Line), π.over a' a ∧ π.overLine L' L ∧ a'.onLine L' → a.onLine L

axiom over_on_line' : ∀ (π : Plane) (a' : _root_.Point) (L' : _root_.Line) (a : Point)
  (L : Line), π.over a' a ∧ π.overLine L' L ∧ a.onLine L → a'.onLine L'

axiom over_between : ∀ (π : Plane) (a' b' c' : _root_.Point) (a b c : Point),
  π.over a' a ∧ π.over b' b ∧ π.over c' c ∧ _root_.between a' b' c' → between a b c

axiom over_between' : ∀ (π : Plane) (a' b' c' : _root_.Point) (a b c : Point),
  π.over a' a ∧ π.over b' b ∧ π.over c' c ∧ between a b c → _root_.between a' b' c'

axiom over_dist : ∀ (π : Plane) (a' b' : _root_.Point) (a b : Point),
  π.over a' a ∧ π.over b' b → dist a b = |(a'─b')|

axiom over_angle : ∀ (π : Plane) (a' b' c' : _root_.Point) (a b c : Point),
  π.over a' a ∧ π.over b' b ∧ π.over c' c → angle a b c = ∠ a':b':c'

axiom over_area : ∀ (π : Plane) (a' b' c' : _root_.Point) (a b c : Point),
  π.over a' a ∧ π.over b' b ∧ π.over c' c → area a b c = Triangle.area △ a':b':c'

/-! Measures -/

axiom dist_symm : ∀ (a b : Point), dist a b = dist b a

axiom dist_nonneg : ∀ (a b : Point), 0 ≤ dist a b

axiom dist_zero : ∀ (a b : Point), dist a b = 0 → a = b

axiom dist_self : ∀ (a : Point), dist a a = 0

axiom angle_symm : ∀ (a b c : Point), a ≠ b ∧ c ≠ b → angle a b c = angle c b a

axiom area_symm_1 : ∀ (a b c : Point), area a b c = area b c a

axiom area_symm_2 : ∀ (a b c : Point), area a b c = area a c b

/-! The volume of a tetrahedron -/

axiom volume_nonneg : ∀ (a b c d : Point), 0 ≤ volume a b c d

axiom volume_symm_1 : ∀ (a b c d : Point), volume a b c d = volume b a c d

axiom volume_symm_2 : ∀ (a b c d : Point), volume a b c d = volume a c b d

axiom volume_symm_3 : ∀ (a b c d : Point), volume a b c d = volume a b d c

/-- Four points on a plane make no solid. -/
axiom volume_zero : ∀ (a b c d : Point) (π : Plane),
  a.onPlane π ∧ b.onPlane π ∧ c.onPlane π ∧ d.onPlane π → volume a b c d = 0

/-- A triangle and a point off its plane make a solid. -/
axiom volume_pos : ∀ (a b c d : Point) (L : Line) (π : Plane),
  a ≠ b ∧ a.onLine L ∧ b.onLine L ∧ ¬ c.onLine L ∧ a.onPlane π ∧ b.onPlane π ∧
  c.onPlane π ∧ ¬ d.onPlane π → 0 < volume a b c d

/-- A tetrahedron cut through an edge `bc` and a point `x` of the opposite edge `ad`. -/
axiom volume_split : ∀ (a b c d x : Point),
  between a x d → volume a b c d = volume a b c x + volume x b c d

/-- Def. 11.10: tetrahedra with equal edges are equal. -/
axiom volume_congr : ∀ (a b c d e f g h : Point),
  dist a b = dist e f ∧ dist a c = dist e g ∧ dist a d = dist e h ∧
  dist b c = dist f g ∧ dist b d = dist f h ∧ dist c d = dist g h →
  volume a b c d = volume e f g h

end Space
