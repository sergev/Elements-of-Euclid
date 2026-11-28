import SystemE
import Elements.Book4.Lemmas
import Elements.Book4.Prop01
import Elements.Book4.Prop02
import Elements.Book4.Prop03
import Elements.Book4.Prop04
import Elements.Book4.Prop05
import Elements.Book4.Prop06
import Elements.Book4.Prop07
import Elements.Book4.Prop08
import Elements.Book4.Prop09
import Elements.Book4.Prop10
import Elements.Book4.Prop11
import Elements.Book4.Prop12
import Elements.Book4.Prop13
import Elements.Book4.Prop14
import Elements.Book4.Prop15
import Elements.Book4.Prop16

/-
Book 4: figures inscribed in and circumscribed about circles.

Conventions. System E has no polygons. A figure is its vertices, in order around it:
triangle `a b c`, square `a b c d`, pentagon `a b c d e`, hexagon `a b c d e f`, with the
lines of its sides, `AB`, `BC`, …, ending with the side back to `a`. A figure is convex:
each side's line has the other vertices on one side. The definitions are in
`SystemE/Book4.lean`:
- `quadrilateral`, `pentagon`, `hexagon`: the vertices on the sides' lines, convex. A
  triangle is Book 1's `formTriangle a b c AB BC CA`.
- Def. 1.22, `square a b c d AB BC CD DA`: a quadrilateral with equal sides and right
  angles.
- `equilateralPentagon a b c d e`, `equiangularPentagon a b c d e`, and the same for
  hexagons: equal sides, and equal angles at the vertices, written out.
  `equiangularTriangles a b c d e f`: the angles at `a`, `b`, `c` equal those at `d`, `e`,
  `f`. Equal chords give equal circumferences (Prop. 3.28), so these are stated with
  lengths and angles, not arcs.
- Defs. 4.3 and 4.6, `inscribedTriangle a b c α` (and `inscribedQuadrilateral`, …): each
  vertex is on the circle. The figure is inscribed in the circle, and the circle
  circumscribed about the figure.
- Defs. 4.4 and 4.5, `circumscribedTriangle a b c AB BC CA p q r α` (and for
  quadrilaterals and pentagons): each side's line touches the circle (Def. 3.2), `AB`
  at `p` and so on, at a point between the side's ends. The figure is circumscribed
  about the circle, and the circle inscribed in the figure.
- Def. 4.7, `insertedInto a b α`: a straight line inserted into a circle, both ends on it.

Prop. 4.16. Euclid constructs one side of the fifteen-sided figure and says the rest
follow. The statement is that the side `BE` cuts off a fifteenth of the circumference,
`α.arc b e c * 15 = α.circumference`, the circumference `BE` away from a point `C` of the
circle (Book 3's circumferences). The proof has it, as Euclid does, as half the
difference of the triangle's and the pentagon's circumferences.

Prop. 4.1 inserts the line from a given point of the circle, the end of Euclid's
diameter, so that Prop. 4.10 can insert it from `B`. Props. 4.11 and 4.15 need Prop. 3.27
for circumferences greater than semicircles (`proposition_11_greater`), proved from the
Book 3 case by Prop. 3.22. The figures Euclid reads positions off are proved convex
(`pentagon_of_circle`, `proposition_12_pentagon`, `proposition_15_hexagon`); his remarks
after 4.15 and 4.16, given without proof, are left out.
-/
