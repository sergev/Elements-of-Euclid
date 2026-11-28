import SystemE.Book3

/-!
Book 4's definitions, over System E's relations and Book 3's. System E has no polygons:
a figure is its vertices, in order around it, and the lines of its sides. A figure is
convex: each side's line has the other vertices on one side.
-/

/-- A quadrilateral `abcd`, convex, with sides on `AB`, `BC`, `CD`, `DA`. -/
@[simp]
abbrev quadrilateral (a b c d : Point) (AB BC CD DA : Line) : Prop :=
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine b c BC ∧
  distinctPointsOnLine c d CD ∧ distinctPointsOnLine d a DA ∧
  c.sameSide d AB ∧ d.sameSide a BC ∧ a.sameSide b CD ∧ b.sameSide c DA

/-- A pentagon `abcde`, convex, with sides on `AB`, `BC`, `CD`, `DE`, `EA`. -/
@[simp]
abbrev pentagon (a b c d e : Point) (AB BC CD DE EA : Line) : Prop :=
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine b c BC ∧
  distinctPointsOnLine c d CD ∧ distinctPointsOnLine d e DE ∧
  distinctPointsOnLine e a EA ∧
  c.sameSide d AB ∧ d.sameSide e AB ∧ d.sameSide e BC ∧ e.sameSide a BC ∧
  e.sameSide a CD ∧ a.sameSide b CD ∧ a.sameSide b DE ∧ b.sameSide c DE ∧
  b.sameSide c EA ∧ c.sameSide d EA

/-- A hexagon `abcdef`, convex, with sides on `AB`, `BC`, `CD`, `DE`, `EF`, `FA`. -/
@[simp]
abbrev hexagon (a b c d e f : Point) (AB BC CD DE EF FA : Line) : Prop :=
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine b c BC ∧
  distinctPointsOnLine c d CD ∧ distinctPointsOnLine d e DE ∧
  distinctPointsOnLine e f EF ∧ distinctPointsOnLine f a FA ∧
  c.sameSide d AB ∧ d.sameSide e AB ∧ e.sameSide f AB ∧
  d.sameSide e BC ∧ e.sameSide f BC ∧ f.sameSide a BC ∧
  e.sameSide f CD ∧ f.sameSide a CD ∧ a.sameSide b CD ∧
  f.sameSide a DE ∧ a.sameSide b DE ∧ b.sameSide c DE ∧
  a.sameSide b EF ∧ b.sameSide c EF ∧ c.sameSide d EF ∧
  b.sameSide c FA ∧ c.sameSide d FA ∧ d.sameSide e FA

/-- Triangles `abc` and `def` are equiangular, the angles at `a`, `b`, `c` equal to those at
`d`, `e`, `f`. -/
@[simp]
abbrev equiangularTriangles (a b c d e f : Point) : Prop :=
  ∠ b:a:c = ∠ e:d:f ∧ ∠ a:b:c = ∠ d:e:f ∧ ∠ a:c:b = ∠ d:f:e

/-- Def. 1.22: the quadrilateral `abcd` is a square, equilateral and right-angled. -/
@[simp]
abbrev square (a b c d : Point) (AB BC CD DA : Line) : Prop :=
  quadrilateral a b c d AB BC CD DA ∧
  |(a─b)| = |(b─c)| ∧ |(b─c)| = |(c─d)| ∧ |(c─d)| = |(d─a)| ∧
  ∠ d:a:b = ∟ ∧ ∠ a:b:c = ∟ ∧ ∠ b:c:d = ∟ ∧ ∠ c:d:a = ∟

/-- The pentagon `abcde` is equilateral. -/
@[simp]
abbrev equilateralPentagon (a b c d e : Point) : Prop :=
  |(a─b)| = |(b─c)| ∧ |(b─c)| = |(c─d)| ∧ |(c─d)| = |(d─e)| ∧ |(d─e)| = |(e─a)|

/-- The pentagon `abcde` is equiangular. -/
@[simp]
abbrev equiangularPentagon (a b c d e : Point) : Prop :=
  ∠ e:a:b = ∠ a:b:c ∧ ∠ a:b:c = ∠ b:c:d ∧ ∠ b:c:d = ∠ c:d:e ∧ ∠ c:d:e = ∠ d:e:a

/-- The hexagon `abcdef` is equilateral. -/
@[simp]
abbrev equilateralHexagon (a b c d e f : Point) : Prop :=
  |(a─b)| = |(b─c)| ∧ |(b─c)| = |(c─d)| ∧ |(c─d)| = |(d─e)| ∧ |(d─e)| = |(e─f)| ∧
  |(e─f)| = |(f─a)|

/-- The hexagon `abcdef` is equiangular. -/
@[simp]
abbrev equiangularHexagon (a b c d e f : Point) : Prop :=
  ∠ f:a:b = ∠ a:b:c ∧ ∠ a:b:c = ∠ b:c:d ∧ ∠ b:c:d = ∠ c:d:e ∧ ∠ c:d:e = ∠ d:e:f ∧
  ∠ d:e:f = ∠ e:f:a

/-- Defs. 4.3 and 4.6: the triangle `abc` is inscribed in `α`, and `α` circumscribed about
it: each vertex is on the circumference. -/
@[simp]
abbrev inscribedTriangle (a b c : Point) (α : Circle) : Prop :=
  a.onCircle α ∧ b.onCircle α ∧ c.onCircle α

/-- Defs. 4.3 and 4.6, for the quadrilateral `abcd`. -/
@[simp]
abbrev inscribedQuadrilateral (a b c d : Point) (α : Circle) : Prop :=
  a.onCircle α ∧ b.onCircle α ∧ c.onCircle α ∧ d.onCircle α

/-- Defs. 4.3 and 4.6, for the pentagon `abcde`. -/
@[simp]
abbrev inscribedPentagon (a b c d e : Point) (α : Circle) : Prop :=
  a.onCircle α ∧ b.onCircle α ∧ c.onCircle α ∧ d.onCircle α ∧ e.onCircle α

/-- Defs. 4.3 and 4.6, for the hexagon `abcdef`. -/
@[simp]
abbrev inscribedHexagon (a b c d e f : Point) (α : Circle) : Prop :=
  a.onCircle α ∧ b.onCircle α ∧ c.onCircle α ∧ d.onCircle α ∧ e.onCircle α ∧ f.onCircle α

/-- Defs. 4.4 and 4.5: the triangle `abc` is circumscribed about `α`, and `α` inscribed in
it: each side touches the circle, `AB` at `p`, `BC` at `q`, `CA` at `r`, between its ends. -/
@[simp]
abbrev circumscribedTriangle (a b c : Point) (AB BC CA : Line) (p q r : Point)
    (α : Circle) : Prop :=
  AB.touchesCircleAt α p ∧ BC.touchesCircleAt α q ∧ CA.touchesCircleAt α r ∧
  between a p b ∧ between b q c ∧ between c r a

/-- Defs. 4.4 and 4.5, for the quadrilateral `abcd`, touching at `p`, `q`, `r`, `s`. -/
@[simp]
abbrev circumscribedQuadrilateral (a b c d : Point) (AB BC CD DA : Line) (p q r s : Point)
    (α : Circle) : Prop :=
  AB.touchesCircleAt α p ∧ BC.touchesCircleAt α q ∧ CD.touchesCircleAt α r ∧
  DA.touchesCircleAt α s ∧ between a p b ∧ between b q c ∧ between c r d ∧ between d s a

/-- Defs. 4.4 and 4.5, for the pentagon `abcde`, touching at `p`, `q`, `r`, `s`, `t`. -/
@[simp]
abbrev circumscribedPentagon (a b c d e : Point) (AB BC CD DE EA : Line)
    (p q r s t : Point) (α : Circle) : Prop :=
  AB.touchesCircleAt α p ∧ BC.touchesCircleAt α q ∧ CD.touchesCircleAt α r ∧
  DE.touchesCircleAt α s ∧ EA.touchesCircleAt α t ∧
  between a p b ∧ between b q c ∧ between c r d ∧ between d s e ∧ between e t a

/-- Def. 4.7: the straight line `ab` is inserted into `α`, its ends on the circumference. -/
@[simp]
abbrev insertedInto (a b : Point) (α : Circle) : Prop :=
  a.onCircle α ∧ b.onCircle α
