import Elements.Book11.Definitions
import Elements.Book11.Lemmas

/-
Book 11: elementary stereometry.

## Space

System E is one plane, with global sorts `Point`, `Line`, `Circle`. Space has its own,
in namespace `Space` (`SystemE/Theory/Sorts/Space.lean`): `Space.Point`, `Space.Line`,
`Space.Plane`; `p.onLine L`, `p.onPlane π`, `L.inPlane π`, `Space.between`,
`p.sameSide q π` (sides of a plane); the measures `Space.dist`, `Space.angle`,
`Space.area` (a triangle) and `Space.volume` (a tetrahedron), reals as in System E, the
right angle System E's `∟`. `SystemE/Space.lean` collects them; Books 1–10 don't import
it.

## Axioms

The rules (`SystemE/Theory/Inferences/Space.lean`) are in System E's form, so that
saturation uses them, and each is true in ℝ³; the constructions are in
`SystemE/Theory/Constructions/Space.lean`:
- incidence, Hilbert I.1–I.8: two points determine a line, three points not on a line a
  plane; a line with two points on a plane is in it; two planes with a common point
  have another; a point off any plane;
- separation by a plane: two sides, a segment between them crosses it, a ray from it
  stays on one side;
- every plane carries System E's plane: `π.over a' a` (`a'` of System E is the point `a`
  of `π`) and `π.overLine L' L`, one-to-one both ways and onto, preserving incidence,
  `between`, length, angle and area. ℝ³: an isometry from ℝ² onto the plane;
- volume of a tetrahedron, as System E's area of a triangle: nonnegative, symmetric,
  zero on a plane and positive off it, additive when cut through an edge and a point of
  the opposite edge, and equal for tetrahedra with equal edges (Def. 11.10, "equal and
  similar", the solid counterpart of superposition). ℝ³: |det|/6.

Fitzpatrick's note to 11.1: Euclid's proofs of 11.1–11.3 are not rigorous, and they
are properly axioms. They are proved from the incidence axioms, and their doc comments
say that Euclid's argument is not followed.

## Saturation

The engine (`SaturateCore.lean`) takes its object sorts from its configuration;
`SystemE/Space.lean` adds space's, and the space versions of the lemmas it uses for
distinct points and lines. Space's measures are metric atoms, with their symmetries.
Because transport is a relation, saturation moves facts between space and a plane:
pull the points of a figure back (`Space.pull_point`, `Space.pull_line`), apply Book 1
or Book 6 to the System E figure with `euclid_apply`, and its conclusions come back
through `over_dist`, `over_angle`. Book 11 has no SMT (`systemE.smt` is off): every step
is saturation's, or a Lean term.

## Definitions (`Definitions.lean`)

- Def. 11.3, `RightToPlane a b π`: `ab` at right angles to `π` at `b`, with every line
  joined to it in the plane: `∀ c`, used by instantiating it.
- Def. 11.4, `PlaneRightToPlane π σ`; Def. 11.8, `ParallelPlanes π σ`; parallel lines in
  space, `Parallel L M` (Fitzpatrick's note to 11.6: in one plane, not meeting).

## Magnitudes

`Volume` (positive reals, `Elements/Book5/Plane.lean`) is a Book 5 magnitude, with
`Length` and `Area`; `len a b h` is the length of a straight line in space. Ratios are
Book 5's `Proportion`.
-/
