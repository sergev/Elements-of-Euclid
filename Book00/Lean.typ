#import "../functions.typ": chapter, no-footer

#chapter([Reading the Lean Proofs], [READING THE LEAN PROOFS])

#v(1em)

This edition gives each proposition of the books it contains twice. First comes Euclid's text in Richard Fitzpatrick's translation, then a formal version written in Lean 4, a programming language and proof assistant. Each proposition's formal statement and proof is printed after the English, under the heading _Formalization_. The proofs of Book 1 come from LeanEuclid, by L. Murphy, K. Yang, J. Sun, Z. Li, A. Anandkumar and X. Si, "Autoformalizing Euclidean Geometry", ICML 2024, distributed under the MIT license. The proofs of Books 2–5 were written for this edition: Books 2–4 in the same system, and Book 5 in plain Lean.

The Lean proofs are written in System E, a formal system that J. Avigad, E. Dean and J. Mumma designed to follow Euclid closely ("A formal system for Euclid's Elements", _Review of Symbolic Logic_ 2, 2009). In particular, it can draw the conclusions that Euclid reads off his diagrams. The result is that a formal proof reads step for step like Euclid's text, and seldom like an exercise in coordinates.

== Objects

System E has six sorts of objects: `Point`, `Line`, `Circle`, segments, angles and triangles. Points, lines and circles are primitive, and nothing is said about what they are. Segments, angles and triangles are made from points:

#table(
  columns: (auto, 1fr),
  stroke: none,
  inset: (x: 0pt, y: 3pt),
  column-gutter: 1.5em,
  [`(a─b)`], [the segment (finite straight-line) from $a$ to $b$],
  [`|(a─b)|`], [its length, a real number (`ℝ`)],
  [`∠ a:b:c`], [the size of the angle at $b$ contained by $b a$ and $b c$],
  [`∟`], [a right-angle],
  [`△ a:b:c`], [the triangle $a b c$, whose `area` is a real number],
  [`▱ a:b:c:d`], [the area of the parallelogram with sides $a b$, $c d$, $a c$, $b d$: the triangles $a c d$ and $a b d$ cut off by the diagonal $a d$],
)

Points are written in lowercase and lines in capitals. The names match Euclid's letters, so the point $C$ of the figure is `c` and the straight-line through $A$ and $B$ is `AB`. A line in System E is the whole infinite line, and Euclid's finite straight-lines are segments.

== Relations

#table(
  columns: (auto, 1fr),
  stroke: none,
  inset: (x: 0pt, y: 3pt),
  column-gutter: 1.5em,
  [`a.onLine L`], [point $a$ lies on line $L$],
  [`between a b c`], [$b$ lies strictly between $a$ and $c$ on one line],
  [`a.sameSide b L`], [$a$ and $b$ are on the same side of $L$, and not on it],
  [`a.opposingSides b L`], [$a$ and $b$ are on opposite sides of $L$],
  [`a.onCircle α`, `a.insideCircle α`], [$a$ is on, or inside, the circle $alpha$],
  [`a.isCentre α`], [$a$ is the center of $alpha$],
  [`distinctPointsOnLine a b L`], [$a eq.not b$, and both lie on $L$],
  [`formTriangle a b c AB BC AC`], [$a$, $b$, $c$ are the vertices of a triangle with sides on the three distinct lines],
  [`formParallelogram a b c d …`], [the four points and lines form a parallelogram],
)

The usual logical signs connect them: `∧` (and), `∨` (or), `¬` (not), `→` (implies), `∀` (for all), `∃` (there exists).

== Theorems

A proposition is a `theorem` with a name and a statement, followed by `:=` `by` and the proof. Here is Proposition 1:

```lean
theorem proposition_1 : ∀ (a b : Point) (AB : Line),
  distinctPointsOnLine a b AB →
  ∃ c : Point, |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)| :=
```

It says: for any two distinct points $a$ and $b$ on a line, there is a point $c$ whose distances to $a$ and $b$ both equal $a b$. Then $a b c$ is an equilateral triangle. Euclid's problems ("to construct…") become statements that the object exists. His theorems ("I say that…") become implications. A name with primes, like `proposition_5'`, is a variant of the same proposition: a special case, or a restatement that later proofs find easier to use.

== Proofs

A proof is a list of steps called _tactics_. Four of them do almost all the work:

#table(
  columns: (auto, 1fr),
  stroke: none,
  inset: (x: 0pt, y: 3pt),
  column-gutter: 1.5em,
  [`euclid_intros`], [Take the given objects and hypotheses ("Let $A B$ be the given finite straight-line").],
  [`euclid_apply R … as x`], [Apply a construction, postulate or earlier proposition `R` to the named objects. With `as`, give names to the new objects it produces ("let the circle $B C D$ be drawn").],
  [`euclid_assert P`], [State an intermediate fact `P` and prove it at once ("thus $A C$ is equal to $A B$").],
  [`euclid_finish`], [Close the proof ("which is the very thing it was required to show").],
)

The other tactics are ordinary Lean. `have h : P := by …` proves a lemma inside the proof. `use c` names the object that an existential statement asks for. `by_contra` begins a proof by contradiction.

The basic rules have their own names, for example:
- `line_from_points` (Post.~1);
- `circle_from_points` (Post.~3);
- `intersection_circles` and `intersection_lines`, which take a point where two circles or two lines meet;
- `extend_point`, which extends a line past a point;
- `superposition`, Euclid's moving of one figure onto another, as in Prop.~1.4.

The proof of Proposition 1 then reads like Euclid's:

```lean
  euclid_intros
  euclid_apply circle_from_points a b as BCD
  euclid_apply circle_from_points b a as ACE
  euclid_apply intersection_circles BCD ACE as c
  euclid_apply point_on_circle_onlyif a b c BCD
  euclid_apply point_on_circle_onlyif b a c ACE
  use c
  euclid_finish
```

== Rectangles and squares

Book 2 speaks of "the rectangle contained by $A B$ and $C D$" and "the square on $A B$". The formal statements write these as products of lengths: `|(a─b)| * |(c─d)|` and `|(a─b)| * |(a─b)|`. "Twice" is `2 * …`. Prop.~1.47 already uses this form. The bridge to figures is the rule `rectangle_area`, which says that the area of a constructed rectangle, as two triangles cut off by a diagonal, is the product of its sides. The rules `parallelogram_area` and `sum_parallelograms_area` say that a parallelogram has the same area whichever diagonal cuts it, and that a parallelogram cut by a parallel to two of its sides is the sum of the two parts. The proofs write the area of a parallelogram as `▱ a:b:c:d`, so that `▱ d:e:a:b = |(a─b)| * |(a─d)|` reads "the rectangle $D B$ is the rectangle contained by $A B$, $A D$".

Written this way, most of Book 2 consists of identities of algebra, which could be proved without any figure. The proofs in this edition do not take that shortcut. Each one draws Euclid's figure and argues with its areas, as he does.

Book 2 adds a few lemmas of its own, printed after its definitions:
- `rectangle_on`, a rectangle on a given line with a given height, drawn as in Prop.~1.46;
- `parallel_between`, which says that parallel lines keep the order of points.

Euclid reads such orders off his figure, and the proofs mark the places with `-- Missed by Euclid.` Three proofs also have a lemma of their own: `proposition_4_figure` is the figure of 2.4, which 2.7 uses again; `proposition_8_sums` adds up the areas of Euclid's nine pieces; and `proposition_14_lemma` is the semicircle construction. Prop.~2.13 has a second form, `proposition_13'`, for the case in which the perpendicular falls outside the triangle.

== Circles

In System E a line that meets a circle "intersects" it only if it cuts it, at two points, and likewise for two circles. Book 3's definitions are written with these relations:

#table(
  columns: (auto, 1fr),
  stroke: none,
  inset: (x: 0pt, y: 3pt),
  column-gutter: 1.5em,
  [`L.touchesCircleAt α a`], [the line $L$ touches $alpha$ at $a$: it meets the circle there and does not cut it (Def.~3.2)],
  [`α.touchesCircleAt β a`], [the circles touch at $a$: they meet there and do not cut (Def.~3.3)],
  [`α.touchesInternallyAt β a`], [they touch, $alpha$ within $beta$: every point inside $alpha$ is inside $beta$],
  [`α.touchesExternallyAt β a`], [they touch, each outside the other: no point is inside both],
  [`equalCircles α β c₁ p₁ c₂ p₂`], [equal circles, with equal radii $c_1 p_1$ and $c_2 p_2$ (Def.~3.1)],
  [`c.onSegment α a b AB s`], [$c$ is on the circumference of the segment of $alpha$ on the chord $a b$, on the side of $s$; the angle in the segment is `∠ a:c:b` (Defs.~3.6, 3.8)],
  [`similarSegments α a b AB x β c d CD y`], [the segments admit equal angles, `∠ a:x:b = ∠ c:y:d` (Def.~3.11)],
)

Euclid compares segments and circumferences as figures and magnitudes. In Prop.~3.24 he applies one segment to another. System E's superposition moves only triangles, so the proof applies the triangle on the chord whose apex is the center. Then it shows, by Prop.~3.23, that the circle about the image of the center is the other segment's circle. "Equal segments" are thus segments on equal chords of equal circles, which coincide when applied.

System E has no circumferences, so Book 3 adds them. `α.arc b c s` is the circumference of $alpha$ from $b$ to $c$ on the side of the chord away from $s$, the one on which an angle at $s$ stands (Def.~3.9), and `α.circumference` is the whole circle. Their axioms are printed after Book 3's definitions. They say only what Euclid assumes of magnitudes: a circumference is the same from either end and is positive; the two circumferences on a chord make the whole circle; a point on a circumference divides it into two parts (C.N.~2); equal circles have equal circumferences; and equal segments have equal circumferences (C.N.~4). Props.~3.26--3.30 are proved from these.

Some positions Euclid leaves out are proved as separate cases. Prop.~3.20 holds for the center on either side of the chord, or on it (`proposition_20'`, `proposition_20''`), and Prop.~3.21 needs these cases for segments not greater than a semicircle. Prop.~3.27 at the circumference assumes circumferences less than semicircles, as in Euclid's figure.

Two claims are left out. In Props.~3.16 and 3.31, Euclid compares the "angle of the semicircle" and the horn angle between a circle and its tangent with rectilinear angles. These angles are contained by a curve, and System E has only rectilinear ones. What makes the claims true is proved: no straight line falls between the tangent and the circle (`proposition_16'`).

== Figures in and about circles

System E has no polygons. Book 4 writes a figure as its vertices, in order around it, with the lines of its sides: a triangle `a b c` with sides on `AB`, `BC`, `CA`, a square `a b c d`, a pentagon `a b c d e`, a hexagon `a b c d e f`. A triangle is Book 1's `formTriangle`. The other figures are convex: each side's line has the other vertices on one side. Book 4's definitions are written out for each number of sides:

#table(
  columns: (auto, 1fr),
  stroke: none,
  inset: (x: 0pt, y: 3pt),
  column-gutter: 1.5em,
  [`quadrilateral a b c d AB BC CD DA`], [the vertices on the sides' lines, convex; likewise `pentagon`, `hexagon`],
  [`square a b c d AB BC CD DA`], [a quadrilateral with equal sides and right angles (Def.~1.22)],
  [`equilateralPentagon a b c d e`], [its sides are equal; likewise for hexagons],
  [`equiangularPentagon a b c d e`], [its angles at the vertices are equal; likewise for hexagons],
  [`equiangularTriangles a b c d e f`], [the angles at $a$, $b$, $c$ are equal to those at $d$, $e$, $f$],
  [`inscribedTriangle a b c α`], [each vertex is on $alpha$: the triangle is inscribed in the circle, and the circle circumscribed about it (Defs.~4.3, 4.6); likewise for the other figures],
  [`circumscribedTriangle a b c AB BC CA p q r α`], [each side touches $alpha$, $A B$ at $p$, $B C$ at $q$, $C A$ at $r$, between its ends: the triangle is circumscribed about the circle, and the circle inscribed in it (Defs.~4.4, 4.5); likewise for quadrilaterals and pentagons],
  [`insertedInto a b α`], [the straight line $a b$ is inserted into $alpha$, its ends on the circle (Def.~4.7)],
)

Equal sides of a figure in a circle cut off equal circumferences (Prop.~3.28), so the definitions speak of lengths and angles, not of circumferences. Prop.~4.16 is the exception. Euclid constructs one side of the fifteen-sided figure and says the rest follow, so the statement is about that side alone: it cuts off a fifteenth of the circumference, `α.arc b e c * 15 = α.circumference`. The proof finds it, as Euclid does, as half the difference of the triangle's and the pentagon's circumferences.

Book 4 adds lemmas of its own, printed after its definitions. Most are facts Euclid reads off his figure: a line touching a circle at a given point (`exists_tangent`); the tangents at the ends of a chord, not a diameter, meet (`tangents_meet`); the center is on the circle's side of a tangent; a perpendicular falls on a side when the angles at its ends are less than right angles (`foot_between`); and four or five points of a circle in the right order make a convex figure (`quadrilateral_of_circle`, `pentagon_of_circle`). Prop.~4.1 inserts its line from a given point of the circle, as Euclid's construction does, so that Prop.~4.10 can insert it from $B$. Props.~4.11 and 4.15 compare angles on circumferences greater than semicircles. Book 3's Prop.~3.27 at the circumference assumes them less, so `proposition_11_greater` proves the greater case from it by Prop.~3.22.

Euclid's remarks after Props.~4.15 and 4.16 are left out. He says, without proof, that a hexagon and a fifteen-sided figure can be circumscribed about a circle, and a circle inscribed in and circumscribed about them, "similarly to the pentagon". For the fifteen-sided figure he also says that the other sides follow by inserting lines equal to the first.

== Proportion

Book 5 is not about figures. Its straight lines stand for magnitudes of any kind, lines, areas or angles, so System E is not used: the proofs are plain Lean, without diagram rules. They are printed like the others.

A kind of magnitude is a type `M` with the class `Magnitude M`, printed after Book 5's definitions. Magnitudes of one kind can be added, in any order and grouping, and compared. Each is less than its sum with another, so none is zero. The lesser can be taken away from the greater, leaving a remainder. And some multiple of each exceeds any other (Def.~5.4, Archimedes' axiom). A multiple `n • a`, with `n : ℕ+`, is $a$ taken $n$ times, $n gt.eq 1$; equal multiples are taken the same number of times. Euclid proves what multiples do: a multiple of a sum, a sum of multiples, and a multiple of a multiple are Props.~5.1–5.3. They are proved here by induction on the multiple, the formal form of Euclid's dividing the multiple into parts equal to the magnitude, and not taken from Mathlib, whose lemmas on multiples would do his work for him. What he takes for granted, that equal multiples of equal magnitudes are equal and that the greater multiple is greater, is proved once with the class.

#table(
  columns: (auto, 1fr),
  stroke: none,
  inset: (x: 0pt, y: 3pt),
  column-gutter: 1.5em,
  [`Proportion a b c d`], [$a : b :: c : d$ (Def.~5.5): for all $m$, $n$, `n • b < m • a ↔ n • d < m • c`, `m • a = n • b ↔ m • c = n • d` and `m • a < n • b ↔ m • c < n • d`],
  [`GreaterRatio a b c d`], [$a : b$ is greater than $c : d$ (Def.~5.7): `∃ m n, n • b < m • a ∧ ¬ n • d < m • c`],
  [`SquaredRatio c d a b`], [$c : d$ is the squared ratio of $a : b$ (Def.~5.9): `∃ e, Proportion a b b e ∧ Proportion c d a e`. Book 5 doesn't use it; Book 6 is its first user],
  [`sum a`], [the magnitudes `a 0`, …, `a n` added together],
)

There are no real numbers here, and no division. A ratio is never a number: $a : b :: c : d$ is a statement about multiples, as in Euclid. Defining it as $a slash b = c slash d$ would turn most of the book into a line of algebra, and would take for granted the numbers that Eudoxus's theory was made to do without. In `Proportion a b c d`, $a$ and $b$ are of one kind and $c$ and $d$ of another, or the same; where Euclid compares the first with the third (Props.~5.14, 5.16, 5.19, 5.23, 5.25), all four are of one kind. A lesser ratio is a greater one read the other way. Defs.~5.12–5.18 (alternate and inverse ratios, composition, separation, conversion, ex aequali, perturbed proportion) are ways of forming a proportion, and the statements write them out.

"Any number of magnitudes" (Props.~5.1, 5.12, 5.22) is a function on `Fin (n + 1)`, the magnitudes `a 0`, …, `a n`. Euclid argues with two or three of them and says that the rest are alike. His case is proved first, as `proposition_1'` or `proposition_22'`, and then any number by induction, with his case as the step.

Euclid assumes, in Prop.~5.18, that a fourth proportional to three magnitudes exists. It does not follow from the laws of magnitudes, so Prop.~5.18 takes it as a hypothesis, `fourth`, and so does Prop.~5.24, which uses it. Other steps he leaves out are marked as usual. In Prop.~5.5 he divides a magnitude into equal parts, which the laws do not allow; the proof takes a multiple instead, as Simson does. In Prop.~5.8, the case of equal parts goes with the first. Props.~5.9 and 5.10 need that a ratio is not both greater and less than another (`proposition_10_lemma`).

The magnitudes of Book 6 are lengths and areas, printed at the end of Book 5. `Length` and `Area` are two kinds, each the positive reals, with `Length.of a b h` the length $|a b|$ of System E and `Area.triangle`, `Area.parallelogram` the areas. That their sums and remainders exist, and Def.~5.4, here are facts of the reals, not things Euclid proves.

== What is checked, and what is assumed

Euclid often passes over small steps without comment. He says that two circles cut one another, or that a point falls inside an angle, because the figure shows it. In System E, such facts follow by a fixed set of diagrammatic, metric and transfer rules. The tactics `euclid_apply`, `euclid_assert` and `euclid_finish` find these small steps automatically. They apply the rules to the facts at hand, and to the facts so obtained, until the step follows or nothing new appears. Each rule they apply is recorded, so the result is an ordinary Lean proof of the step. When a gap is larger than that, the formal proof has to fill it explicitly. The comment `-- Missed by Euclid.` marks such places, where Euclid relied on a fact that he never proved.

One thing is taken on trust: the points, lines and circles of System E and its rules are _axioms_, as are Book 3's circumferences. They are not derived from a model of the plane, such as pairs of real numbers. Book 5 adds no axioms: the laws of magnitudes are the class `Magnitude`, so each proposition holds for every kind of magnitude that obeys them. Everything else, every step, the order of the steps and the use of each proposition and rule, is checked by Lean. The proofs in this book were checked with Lean 4.36, using a version of System E taken from LeanEuclid and extended for this edition. The command `make check` in the source repository repeats the check.
