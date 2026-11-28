/-
Book 11: elementary stereometry. Design note (Milestone 11, T1), to be reviewed before
any proofs are written. Nothing imports this file yet.

## Sorts

System E is one plane, with global sorts `Point`, `Line`, `Circle`. Space gets its own,
in namespace `Space` (`lean/SystemE/Space.lean`, rules in
`lean/SystemE/Theory/Inferences/Space.lean`, imported only by Book 11 and later):

- `Space.Point`, `Space.Line`, `Plane`;
- `p.onLine L`, `p.onPlane π`, `L.inPlane π`, `Space.between a b c`;
- `Space.dist a b`, `Space.angle a b c`, `Space.area a b c` (a triangle), all reals, as in
  System E; the right angle is System E's `∟`;
- `Space.sameSide p q π`: `p`, `q` on the same side of the plane `π`;
- `Space.volume a b c d`: the tetrahedron `abcd` (below).

## Axioms of space

All in E's form, `∀ objects, literals → literals`, or constructions `∃ …`, so that
saturation can use them. Each is true in ℝ³:

- incidence, Hilbert I.1–I.8: two points determine a line; three points lie on a plane
  (`plane_from_points`), on exactly one if not collinear; a line with two points on a
  plane is in it (`line_in_plane`, I.6); two planes with a common point have another
  (I.7); there are four points not on a plane (I.8). ℝ³: elementary linear algebra.
- separation by a plane: Hilbert's theorem in space, taken in E's form as
  `same_side_symm`, `same_side_trans`, `same_side_pigeonhole`, a segment between
  opposite sides crosses the plane, and its converse. ℝ³: the sign of an affine
  function.
- every plane carries System E's plane. A relation `π.over a' a` (`a'` a point of System
  E, `a` of space) and `π.overLine L' L`, with: `over` points are on `π`; every point
  of `π` is over some `a'` and every `a'` has a point over it (constructions); `over`
  is one-to-one both ways; and it preserves incidence, `between`, `sameSide` of a line
  within the plane, `dist`/length, `angle`/degree and `area`/`Triangle.area`. ℝ³: an
  isometry from ℝ² (System E's model) onto the plane. All planes are copies of one
  plane, so two triangles in different planes may both be pulled back into System E
  and compared there: Book 1's 1.4, 1.8, 1.26 for triangles in space are one step each.
  Circles stay in System E: a circle in space is a circle of the pulled-back figure
  (11.23 needs 3.31, 4.1, 4.5).
- volume of a tetrahedron, like E's area of a triangle: `volume a b c d ≥ 0`, zero exactly
  when the four points are on a plane, unchanged by permuting the vertices, additive
  when the tetrahedron is split by a point between two vertices
  (`volume a b c d = volume a b c x + volume x b c d` for `between a x d`), and equal
  for tetrahedra with the six edges equal (Def. 11.10, "equal and similar"; this is
  the solid counterpart of System E's superposition). ℝ³: |det|/6.

No other axioms. Fitzpatrick's note to 11.1: Euclid's proofs of 11.1–11.3 are not
rigorous, and they are properly axioms. They are stated as theorems and proved from I.6
and I.7 in a few steps; the doc comments say that Euclid's argument is not followed and
quote the note.

## Transport and saturation

The engine (`SaturateCore.lean`) takes its rules from the axioms in
`SystemE.Theory.Inferences.*` and its configured lemmas, and is generic except in two
places: `isObject` knows only `Point`, `Line`, `Circle`, and the metric terms are
`Segment.length`, `Angle.degree`, `Triangle.area`. Change: the object sorts and the
metric heads become part of `Config`, so that Book 11 adds `Space.Point`, `Space.Line`,
`Plane` and `Space.dist`, `Space.angle`, `Space.area`, `Space.volume`. Books 1–10 don't
import the space rules, so their saturation is unchanged (checked by `gaps.sh` and
`make check` times).

Because transport is a relation, saturation moves facts between space and the plane
itself: after `obtain ⟨a', ha⟩ := pull_point π a h` for the vertices of a figure, the
pulled-back figure gets System E's facts, and
`euclid_apply Elements.Book1.proposition_4 …` works on it as in Books 1–6; its
conclusions come back by `over_dist`, `over_angle`.
Steps in space (11.4's "the line is in the plane", 11.13's two perpendiculars) are
closed by saturation over the space rules. Where a step won't saturate, the same
remedies as Books 1–6.

## Definitions (`Elements/Book11/Definitions.lean`)

- Def. 11.3 `Perpendicular L π a`: `a` on `L` and `π`, and right angles with every line
  in `π` through `a`, stated over points (`∀ p q`, …, `angle p a q = ∟`), used as
  Book 3's facts with `∀` are: instantiated.
- Def. 11.4 `PerpendicularPlanes π σ`; Def. 11.8 `ParallelPlanes π σ` (distinct, no
  common point).
- Parallel lines in space (Fitzpatrick's note to 11.6): distinct, in one plane, not
  meeting.
- Def. 11.11 for three plane angles: `SolidAngle d a b c`, apex `d`, the four points not
  on a plane. Equal solid angles (11.26): the three plane angles equal in order, which
  is what Euclid's construction gives. 11.21 is stated for three plane angles, as
  Euclid proves it (Fitzpatrick's note); the general case is not formalized.
- The parallelepiped `Parallelepiped a b c d e f g h`: base `abcd`, `efgh` above it, the
  faces in three pairs of parallel planes. Its volume is a fixed sum of six
  tetrahedra (two prisms of three); 11.24 and 11.28 show the faces are parallelograms
  and the halves equal. Height: the perpendicular from a point of the top to the
  base's plane (11.11).
- The triangular prism (Def. 11.13), for 11.28 and 11.39, with volume three tetrahedra.
  Every two vertices of a prism are on a common face, so equal and similar prisms are
  equal by the axiom for tetrahedra.
- Def. 11.9 (similar solids) for parallelepipeds: equal solid angles, sides about them
  proportional. Def. 11.10 is the volume axiom above.
- Not formalized in Book 11, not used there: Defs. 11.1, 11.2 (solid, surface), 11.5–11.7
  (inclinations), 11.12 (pyramid: Book 12's tetrahedron), 11.14–11.28 (sphere, cone,
  cylinder, the regular solids; cube only as a parallelepiped for 11.38).

## Magnitudes

`Volume`, positive reals, joins `Length` and `Area` in `Elements/Book5/Plane.lean`, so
solids are a Book 5 magnitude; lengths and areas in space are `Length`/`Area` of
`Space.dist`, `Space.area`. Ratios are Book 5's `Proportion` (11.17, 11.25, 11.32–11.34,
11.37); Book 6's `∷` over figures is used inside a pulled-back plane, and comes back as a
`Proportion` of `Length`s. Def. 5.10 for magnitudes (`CubedRatio'`, like Book 6's
`SquaredRatio'`) for 11.33. The steps of Fitzpatrick's notes to 11.34 (equal solids on
equal bases have equal heights; the lesser base, the greater height) and 11.37 (equal
ratios have equal cubed ratios, and conversely) are proved and marked
`-- Missed by Euclid.`

## Example statements (scratch, `tmp/b11/Design.lean`, compiled)

  theorem proposition_4 : ∀ (a b c d : Space.Point) (L M N : Space.Line) (π : Plane),
      a.onLine L ∧ b.onLine L ∧ a.onLine M ∧ c.onLine M ∧ L ≠ M ∧
      b.onPlane π ∧ c.onPlane π ∧ a.onPlane π ∧ d.onLine N ∧ a.onLine N ∧ d ≠ a ∧
      a ≠ b ∧ a ≠ c ∧ angle d a b = ∟ ∧ angle d a c = ∟ → Perpendicular N π a

  theorem proposition_17 : ∀ (a b c d e f : Space.Point) (π σ τ : Plane) …,
      ParallelPlanes π σ ∧ ParallelPlanes σ τ ∧ ParallelPlanes π τ ∧
      a.onPlane π ∧ b.onPlane σ ∧ c.onPlane τ ∧ between a b c ∧
      d.onPlane π ∧ e.onPlane σ ∧ f.onPlane τ ∧ between d e f →
      Proportion (len a b _) (len b c _) (len d e _) (len e f _)

  theorem proposition_21 : ∀ (d a b c : Space.Point), SolidAngle d a b c →
      angle a d b + angle b d c + angle c d a < 4 * ∟

## Risks

- Saturation over two geometries at once may be slow; the transport is the first thing
  T2 tests (1.4 for triangles in two planes).
- The cut of a parallelepiped by a plane (11.25, 11.28) is additive only through a chain
  of tetrahedron splits (a 2–3 flip is four edge splits); that lemma is the cost of
  volume.
- A wrong axiom is not caught by the kernel; the ℝ³ check above is by hand.
-/
