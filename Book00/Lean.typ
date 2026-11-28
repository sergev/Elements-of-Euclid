#import "../functions.typ": chapter, no-footer

#chapter([Reading the Lean Proofs], [READING THE LEAN PROOFS])

#v(1em)

This edition gives each proposition of the books it contains twice. First comes Euclid's text in Richard Fitzpatrick's translation, then a formal version written in Lean 4, a programming language and proof assistant. Each proposition's formal statement and proof is printed after the English, under the heading _Formalization_. The proofs of Book 1 come from LeanEuclid, by L. Murphy, K. Yang, J. Sun, Z. Li, A. Anandkumar and X. Si, "Autoformalizing Euclidean Geometry", ICML 2024, distributed under the MIT license. The proofs of Books 2–7 were written for this edition: Books 2–4 and 6 in the same system, and Books 5 and 7 in plain Lean.

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

== Similar figures

Book 6 applies Book 5's proportion to figures, and its proofs have two kinds of step. The geometric steps are System E's, found as in Books 1–4. The steps about ratios are Book 5's propositions, applied as ordinary Lean terms: the figure gives equal lines, areas and angles, these become equal magnitudes, and a proposition of Book 5 is cited. The search knows nothing of ratios, and ignores them.

A straight line `(a─b)` is a magnitude of the kind `Length`, and a triangle `△a:b:c`, a quadrilateral `□a:b:c:d` or a pentagon `⬠a:b:c:d:e` one of the kind `Area`. System E measures each by a real number, its `size`: the length, or the area. The area of a quadrilateral or pentagon is that of the triangles cut off by the diagonals from its first vertex, so `□a:b:c:d` is `△a:b:c` and `△a:c:d` together. A figure is a magnitude only when it is not degenerate, its size positive. The proportion of figures is written as Euclid writes it:

#table(
  columns: (auto, 1fr),
  stroke: none,
  inset: (x: 0pt, y: 3pt),
  column-gutter: 1.5em,
  [`p ∶ q ∷ r ∶ s`], [as $p$ is to $q$, so is $r$ to $s$ (Def.~5.5), the four figures not degenerate; $p$, $q$ of one kind, $r$, $s$ of one kind, the same or another, so that `(a─b) ∶ (c─d) ∷ △a:b:c ∶ △a:c:d` compares lines with triangles],
  [`SquaredRatio' p q r s`], [$p : q$ is the squared ratio of $r : s$ (Def.~5.9)],
  [`CompoundRatio' p q r s u v`], [$p : q$ is compounded of $r : s$ and $u : v$: as Euclid uses it in Prop.~6.23, the same as $k : m$ with $k : l$ the same as $r : s$ and $l : m$ as $u : v$],
  [`similarTriangles a b c d e f`], [Def.~6.1: the triangles are equiangular, the angles at $a$, $b$, $c$ equal to those at $d$, $e$, $f$, and the sides about the equal angles proportional; likewise `similarQuadrilaterals`, `similarPentagons`, the vertices in corresponding order],
  [`extremeMeanRatio a b c`], [Def.~6.2: $a b$ is cut at $c$, and $a b : a c :: a c : c b$],
)

The statement that a proportion holds includes that its four figures are not degenerate, so a proportion of lines says that their ends are distinct, and needs no separate hypothesis. Small lemmas carry Book 5 over to figures, each citing its proposition: inversely (`inv`, Prop.~5.7 corollary), the same ratio as the same (`trans`, Prop.~5.11), alternately (`alt`, Prop.~5.16), via equality (`exAequali`, Prop.~5.22). Def.~6.3, the height, is used as Prop.~6.1 uses it, triangles with a common vertex and their bases on one line.

Prop.~6.1 lays off "any number" of lines equal to a base, and Prop.~6.9 a part of a line. These are equal segments laid off $m$ times, for every $m$, and that is an induction. Each step of it is a System E construction (Props.~1.3, 1.31, 1.38): the lemmas `multiple_on_line` are printed after Book 6's definitions, with the other lemmas, among them the crossbar (a line inside an angle cuts the base) and the triangle on a given base with given angles.

Where Euclid's figure has the triangles or parallelograms of a proposition side by side, the proof builds that figure. In Prop.~6.4 the second triangle is copied beside the first (Props.~1.3, 1.23, 1.4), and in Prop.~6.15 at the vertex of the first, so that both apply to any two triangles. Props.~6.14 and 6.23 state their parallelograms as Euclid lays them, at a common vertex, and Prop.~6.16 constructs its rectangles so. Prop.~6.12 constructs the fourth proportional of lines that Props.~5.18 and 5.24 assume, and Prop.~6.24 uses it for 5.18. One fact of the model is used: in Prop.~6.31 the fourth proportional for 5.24 is an area, which the figure does not give, and it is taken from the positive reals (`Positive.fourth`).

Some propositions are restricted to the figures defined here. Prop.~6.18 describes triangles and quadrilaterals, Prop.~6.20 is proved for pentagons, as in Euclid's figure, and its corollary for quadrilaterals. In Prop.~6.20 the triangles are shown proportional by Prop.~6.19, being in the squared ratio of the same diagonals, where Euclid compares them through the diagonals $A C$, $F H$. Prop.~6.22 takes Euclid's figure, triangles on two lines and quadrilaterals on the other two. Prop.~6.25 makes a figure similar to a triangle or a quadrilateral, and the given figures of Props.~6.25, 6.28 and 6.29 are those Prop.~1.45 takes, quadrilaterals given as two triangles. Prop.~6.27 is Euclid's case, the defect less than the one on the half. Prop.~6.31 is stated for triangles. Equal similar figures have equal corresponding sides: Euclid takes it for granted in Prop.~6.22, and it is proved here from the squared ratio.

For Prop.~6.33 an angle `∡a:b:c` is a magnitude of the kind `AngleSize`, and a circumference `⌒α:b:c:s` one of the kind `ArcSize`. Euclid lays off any number of circumferences equal to a given one around the circle, and takes the angle they make together, to apply Def.~5.5 to all equal multiples. Past the whole circle such a circumference is not one of Book 3's, and past two right angles such an angle is not one of System E's. But both are measured by real numbers, so their multiples are numbers too, and Def.~5.5 asks only how they compare. Laid round the circle, the angles pass some number of semicircles and leave a remainder within one: an angle at the center, on its circumference. Two multiples compare as their numbers of semicircles, and then as their remainders, which compare as Props.~3.26 and 3.27 say. No axioms are added.

== Numbers

Book 7 is about numbers, and its proofs are plain Lean, like Book 5's. Numbers are Lean's natural numbers `ℕ`. A number is a multitude of units (Defs.~7.1, 7.2), $a > 1$, and the unit is $1$. Euclid's arguments often take the unit where a number may stand, as a quotient that is one, or "as many units as", so a statement takes $a > 0$ wherever its proof allows, and says so.

Multiplication is Def.~7.15: a number multiplies another when the other is added to itself as many times as there are units in the first. The Lean term `a * b` is $a$ taken $b$ times, "$b$ multiplies $a$", and `a * (b + 1) = a * b + a` is Lean's definition of it. "$a$ multiplying $b$ makes $c$" is `c = b * a`, and "$a$ measures $b$ according to the units in $c$" is `b = a * c`, so "$a$ measures $b$" is Mathlib's `a ∣ b`. That `b * a` and `a * b` are equal is Prop.~7.16, so it is not used before. Until then the proofs compute only with the definition: a sum of equal numbers is counted by induction on how many there are, as Euclid divides a number into its parts. Prop.~7.5 proves that $a$ and $d$ taken $n$ times each make $a + d$ taken $n$ times, and Prop.~7.9 that $n$ numbers, each $x$ taken $p$ times, make $x$ taken $n$ times, taken $p$ times.

#table(
  columns: (auto, 1fr),
  stroke: none,
  inset: (x: 0pt, y: 3pt),
  column-gutter: 1.5em,
  [`PartOf a b n`], [$a$ is a part of $b$, the $n$th part (Def.~7.3): `1 < n ∧ b = a * n`],
  [`PartsOf a b m n`], [$a$ is parts of $b$, $m$ of its $n$th parts (Def.~7.4): `1 < m ∧ m < n ∧ ∃ e, a = e * m ∧ b = e * n`],
  [`a ∶ b ∷ c ∶ d`], [the numbers are proportional (Def.~7.20): the first is the same multiple, the same part, or the same parts of the second as the third is of the fourth],
  [`PrimeNumber p`], [a prime number, measured by the unit alone (Def.~7.11)],
  [`PrimeTo a b`], [numbers prime to one another, with the unit alone as a common measure (Def.~7.12)],
  [`Least a b`], [$a$, $b$ are the least of the numbers having the same ratio as them],
  [`GreatestCommonMeasure g a b`], [the greatest number that measures $a$ and $b$ (7.2)],
  [`LeastMeasured c a b`], [the least number that $a$ and $b$ measure (7.34)],
)

The same parts are the same $m$ and $n$, taken as Euclid finds them, not in least terms. Def.~7.20 says nothing of a first number greater than the second that is not a multiple of it, such as $3 : 2 :: 6 : 4$; Euclid's proofs need it, as Prop.~7.13 alternates $2 : 3 :: 4 : 6$ into it, and read it the other way round, the second being the same parts of the first that the fourth is of the third. That is a fourth case of the definition. Proportion of numbers is not Book 5's, and it is not `a * d = b * c`, which is Prop.~7.19. There is no division and no rational number: a ratio of numbers is never $a slash b$. The other definitions, composite, plane, solid, square, cube, similar and perfect numbers, are printed after Book 7's. Odd and even numbers are left to Book 9. Any multitude of numbers (Props.~7.12, 7.14) is a function on `Fin (n + 1)`, as in Book 5; where Euclid takes three numbers (Props.~7.3, 7.33, 7.36), the statement is for three.

The process of Props.~7.1 and 7.2, the lesser number subtracted continually, in turn, from the greater, is a recursion, `remainder a b`: it stops at the remainder equal to the number before it. A unit remains in Prop.~7.1, and the greatest common measure in Prop.~7.2. Each proposition proves its half by induction along the process: a number measuring both measures every remainder (7.1), and the last remainder measures every number before it (7.2). Prop.~7.31's descent, "an infinite series of numbers, each less than the one before, which is impossible in numbers", is an induction on the number.

Mathlib's lemmas do none of Euclid's work. The greatest common measure, numbers prime to one another, primes and the least common multiple are defined here and proved as Euclid proves them, not taken from `Nat.gcd`, `Nat.Coprime`, `Nat.Prime` or `Nat.lcm`. Mathlib supplies what Euclid takes for granted: the order of numbers and the common notions of measuring (a measure of a measure measures, and a measure of a whole and of a part taken away measures the remainder), which are printed with Book 7's lemmas. After Prop.~7.16, its equality may be cited, or a tactic that uses it, with a comment naming it. Associativity of multiplication, which Euclid uses without proof in Props.~7.33 and 7.34, is Mathlib's.

Book 7 uses Book 5's propositions on numbers without proof: Props.~5.7 and 5.9 in Prop.~7.19, 5.13 in Prop.~7.33, and 5.11, that ratios the same as the same ratio are the same as one another, throughout (7.12, 7.14, 7.19, 7.34). They do not follow from Def.~7.20 alone. The parts of a ratio can be counted in many ways, $4$ and $6$ being $2$ taken twice and three times, or the unit taken four and six times, and to join two proportions one needs the parts in least terms, which Book 7 reaches only in Props.~7.20–7.22. They are proved from the model, four numbers being proportional when the product of the outer is the product of the middle, and marked `-- Missed by Euclid.` In Prop.~7.21 Euclid applies Prop.~7.20 to numbers less than the given ones in the same ratio, as if they were the least; the proof takes the least of them, which exist because numbers cannot decrease for ever (`exists_least`, also marked). Prop.~7.33 does the same with three numbers, and there the proof does without: for three numbers, having the same ratio is being the same parts of them, each of each (`SameRatio₃`), and Euclid's argument goes through with those parts in place of his lesser numbers.

== Continued proportion

Book 8 is about numbers in continued proportion, and its proofs are plain Lean on Book 7's basis: the same numbers, multiplication, measuring and proportion, and the same use of Mathlib. Any multitude of numbers is a function on `Fin (n + 1)`, as in Book 7, and its numbers are `a 0`, …, `a n`. Book 8 has no definitions of its own; the phrases of its enunciations are printed after Book 8's title page.

#table(
  columns: (auto, 1fr),
  stroke: none,
  inset: (x: 0pt, y: 3pt),
  column-gutter: 1.5em,
  [`ContinuedIn a r s`], [the numbers are continuously proportional in the ratio of $r$ to $s$: each is to the next as $r$ to $s$],
  [`Continued a`], [continuously proportional: each is to the next as the first to the second],
  [`SameRatios b a`], [$b$ has the same ratios as $a$, each to the next as each to the next],
  [`LeastSeq a`], [the least of those having the same ratios as them: no numbers in the same ratios are each less than each, as `Least` for two],
  [`FallBetween n a b`], [$n$ numbers fall between $a$ and $b$ in continued proportion],
)

The unit may be among the numbers, as in Props.~8.9 and 8.10, and in Book 9's numbers continuously proportional from a unit. With `FallBetween`, "as many numbers as fall between these, so many fall between those" (Props.~8.8–8.10) is the same $n$ on both sides.

Euclid argues with three or four numbers, $A$, $B$, $C$, $D$, and says "similarly" for more. The statements here are for any multitude, and the proofs are inductions whose step is what Euclid does once more. In Prop.~8.2 the least numbers in the ratio of $a$ to $b$, `powers a b n`, are made from those one fewer: $a$ multiplies each of them and $b$ the last, as $A$ multiplying $C$, $D$, $E$ makes $F$, $G$, $H$, and $B$ multiplying $E$ makes $K$. Prop.~8.4 adds one ratio at a time, through the least number measured by the last number found and the next antecedent (Prop.~7.34); the induction carries the fact Euclid's contradiction uses, that the numbers found measure any numbers in the same ratios. Ex aequali along a sequence is Prop.~7.14 taken a step at a time. Two sequences that are both the least in the same ratios are equal, each to each; Euclid takes this for granted in Prop.~8.3, and it is proved in Book 8's lemmas. In Prop.~8.6, "similarly" means the same argument for the numbers from `a i` to `a j`, and the statement says that no earlier number measures a later one: a later may measure an earlier, as $2$ measures $4$ in $4$, $2$, $1$.

A square is `a * a` and a cube `a * a * a` (Defs.~7.18, 7.19). Euclid uses Book 5's squared and cubed ratios (Defs.~5.9, 5.10) and Book 6's compounded ratio for numbers without comment, so they are defined again here with proportion of numbers. Book 5 takes the squared ratio of $a$ to $b$ through the third proportional to $a$ and $b$, which numbers need not have; here $c$ has to $d$ the squared ratio of $a$ to $b$ when some $x$ makes $c : x :: a : b$ and $x : d :: a : b$, and the cubed ratio has two such middle terms. The ratio compounded of $a : b$ and $e : f$ is that of $g$ to $k$, for any $g$, $h$, $k$ with $g : h :: a : b$ and $h : k :: e : f$, as Euclid builds it in Prop.~8.5.

Fitzpatrick notes that Prop.~8.20 is defective: Euclid makes $F$ the number of times $D$ measures $A$, and then uses that $F$ multiplying $E$ makes $C$, which he never shows. It follows from Prop.~7.20, $D$ measuring $A$ as many times as $E$ measures $C$, and the proof says so, marked `-- Missed by Euclid.` His step that $D : E :: A : C$ is the hypothesis, and is skipped. The sides Prop.~8.20 finds may be the unit: one number, $4$, falls between $2$ and $8$, but $2$ is prime and not a plane number. So Props.~8.20 and 8.21 conclude that the numbers are products of sides in proportion, with sides that may be the unit, and so do Props.~8.18, 8.19, 8.26 and 8.27 take them. In Props.~8.22 and 8.23 Euclid argues that a number similar to a square is a square (Def.~7.21), which does not follow, since the sides of a square found by Prop.~8.20 need not be equal ($4$ is $1 times 4$). The proofs use the argument of his Prop.~8.21 instead: the outermost numbers are the least ones in their ratio, $x times x$ and $y times y$, taken the same number of times; $x times x$ measures the given square, so $x$ measures its side (Prop.~8.14), and that number of times is a square.

== Odd and even

Book 9 completes the books on numbers, with the same basis as Books 7 and 8 and the same use of Mathlib. It has no definitions of its own. It uses Book 7's odd and even numbers (Defs.~7.6–7.10), which Book 7 leaves to Book 9, and perfect numbers (Def.~7.22). The definitions of odd and even are printed after Book 9's title page, with Book 9's lemmas.

#table(
  columns: (auto, 1fr),
  stroke: none,
  inset: (x: 0pt, y: 3pt),
  column-gutter: 1.5em,
  [`EvenNumber a`], [divided in half (Def.~7.6): `∃ h, 0 < h ∧ a = h + h`],
  [`OddNumber a`], [not divided in half (Def.~7.7): `0 < a ∧ ¬ EvenNumber a`],
  [`EvenTimesEven a`], [measured by an even number according to an even number (Def.~7.8): `a = e * f`],
  [`EvenTimesOdd a`], [measured by an even number according to an odd number, greater than the unit (Def.~7.9)],
  [`LeastMeasuredSeq c a`], [$c$ is the least number measured by `a 0`, …, `a n`],
)

The unit is odd: it is not divided in half, and Euclid takes it so when he says that a number measuring another does so an even or an odd number of times (Prop.~9.30), and in his sums of odd numbers (9.22, 9.23, 9.29). Def.~7.7's second reading, "differs from an even number by a unit", is a lemma, `a = h + h + 1`, where for the unit $h$ is nothing. The odd number of Def.~7.9 is a number, greater than the unit: else every even number would be even-times-odd, measured by itself according to the unit, and Prop.~9.32 would fail. So the odd half of Prop.~9.33 is greater than the unit. The numbers doubled from the unit are Book 8's `powers 1 2 n`: the unit, the dyad, $4$, and so on; Euclid's numbers doubled from a dyad (9.32) are those after the dyad. The least number measured by any multitude is Euclid's Prop.~7.36 done once more for each number added (7.34, 7.35), by induction; Props.~9.14 and 9.20 take three primes, and are stated for any multitude.

Numbers "continuously proportional from a unit" are `Continued a` with `a 0 = 1`. The number after the unit is `a 1`, and Euclid's third from the unit is `a 2`, counting the unit as the first. The statements of Props.~9.8–9.13 are by index: in Prop.~9.8, `a (2 * k)` is square and `a (3 * k)` cube, for every $k > 0$, where Euclid shows the first of each and says "similarly"; in Prop.~9.10, a square among them, the number after the unit not being square, is some `a (2 * j)`. Prop.~9.11 and its corollary say that `a i` measures `a j` according to `a (j - i)`. Prop.~9.13, used by Props.~9.32 and 9.36, says that every number measuring the last is some `a i`. Euclid proves Props.~9.12 and 9.13 by contradiction, going down from the last number one step at a time; the proofs are inductions with the same steps.

Fitzpatrick notes that Prop.~9.19 is defective. Euclid takes four cases, the three numbers being continuously proportional or not, and the outermost prime to one another or not. In the second, not proportional with the outermost prime, he says that no fourth proportional can be found, and his proof assumes a fifth number that need not exist; and the claim is false: $2$, $4$, $3$ have the fourth proportional $6$. The statement is the true criterion, which his last cases prove (Prop.~7.19): a fourth proportional to $a$, $b$, $c$ exists exactly when $a$ measures $b$ multiplying $c$. In the same way Prop.~9.18 is an "if and only if". In Prop.~9.15 Euclid cites Props.~2.3 and 2.4, about lines, for numbers; the identities are proved by Book 7's multiplication. His last step there, "by separation", from $x x + y y + 2 y x$ prime to $y x$ to $x x + y y + y x$ prime to it, is proved and marked `-- Missed by Euclid.`, as Fitzpatrick notes. So is the step in Prop.~9.31 that a number measuring an odd number is odd. In Prop.~9.34 the number is assumed even, and it is a hypothesis; Euclid's first step, "even-times-even, for it does not have an odd half", holds as Def.~7.8 is stated, the dyad measuring the number according to its half. "Cut in half continually" is an induction on the number.

Prop.~9.36 concludes with Book 7's `Perfect`: the sum of the numbers less than the number made and measuring it is the number. Euclid shows that the number is the sum of the unit, the numbers doubled from it, and as many doubled from the prime sum (by Prop.~9.35), and that it is measured by no others (9.13, 7.19, 7.20, 7.29). A lemma turns this into the sum Def.~7.22 asks for: if the parts of a number are exactly the distinct numbers of a list, the two sums agree.

== Incommensurable magnitudes

Book 10 is plain Lean over Book 5's magnitudes, like Book 5: no System E, and Book 5's propositions are cited as Lean terms, as in Book 6. Its first propositions, 10.1–10.8 and 10.11–10.16, are about magnitudes of any kind; from 10.9 on, its magnitudes are lines and areas, Book 5's `Length` and `Area`. The square on a line, `sq a`, and the rectangle contained by two lines, `rect a b`, are areas, the products of the lengths, as in Book 2. There is still no division, and no rational or irrational number: Mathlib's `Irrational`, `ℚ` and `Real.sqrt` appear in no statement and no step of Euclid's.

#table(
  columns: (auto, 1fr),
  stroke: none,
  inset: (x: 0pt, y: 3pt),
  column-gutter: 1.5em,
  [`Measures c a`], [$c$ measures $a$: `∃ n : ℕ+, a = n • c`],
  [`Commensurable a b`], [some magnitude measures both (Def.~10.1); incommensurable is its negation],
  [`CommensurableInSquare a b`], [the squares on the lines are commensurable (Def.~10.2); `InSquareOnly a b` adds incommensurable in length],
  [`Rational ρ x`], [$x$ is commensurable with the assigned line $rho$ in length, or in square only (Def.~10.3)],
  [`RationalArea ρ A`], [$A$ is commensurable with the square on $rho$ (Def.~10.4)],
  [`MedialArea ρ A`], [$A$ is the rectangle contained by rational lines commensurable in square only (10.21); `Medial ρ x`: the square on $x$ is such an area],
)

Rational and irrational are relative to the assigned line $rho$, a parameter of each proposition, as Euclid's definitions make them; irrational is a negation, and is proved from the hypotheses, as Euclid proves it, never from the irrationality of a real number. "The ratio which a number has to a number" (10.5–10.9) is Book 5's proportion between magnitudes and numbers, so numbers are a kind of magnitude too: `Number`, the positive integers, with `(m : Number)` the number $m$. Book 5's proportion of four numbers agrees with Book 7's (Def.~7.20); Euclid passes from one to the other without comment, and the lemma that they agree is marked `-- Missed by Euclid.`, so that Books 7–9 can be cited (8.11, 8.24, 9.1, 9.2).

A `Length` is a magnitude, not a segment of System E's plane, so the propositions of Books 2 and 6, which are about points, cannot be cited. The facts of theirs that Book 10 uses are lemmas of the model, proved for positive reals and each naming its proposition: rectangles of the same height are as their bases (6.1), squares on proportional lines are proportional (6.22) and the square on a line is to the square on another in the squared ratio (6.20), the square on a sum or a difference (2.4, 2.5, 2.7, 2.9), equal rectangles have reciprocal sides (6.14, 6.16, 6.17), and the right-angled triangle with its perpendicular (6.8). So are the constructions by which Euclid finds lines: a part of a line (6.9), a line cut in a given ratio (6.10), a fourth and a mean proportional (6.12, 6.13), a square equal to an area (2.14), a rectangle applied to a line (1.44), falling short or exceeding by a square (6.28, 6.29), and the line by whose square one square exceeds another, or which squares to two (3.31, 1.47). They are listed after Book 10's definitions, and there are no other facts of the model. Where Euclid divides a magnitude of any kind into equal parts (10.6, and through it 10.7, 10.11–10.13), the kind is assumed `Divisible`, as 5.18 assumes a fourth proportional; lines and areas are.

Props.~10.1 and 10.2 are the first infinite processes in the edition. Taking more than half continually is a sequence of remainders `x : ℕ → M`, each step a hypothesis, and 10.1's proof is an induction on the multiple of the lesser magnitude that exceeds the greater. The process of 10.2, the lesser taken in turn from the greater as often as it can be, is a sequence too, `NeverMeasures r`: it never stops. In 10.3 the process is a recursion that stops, `process a b`, and that it stops is 10.2: the magnitudes are commensurable.

The twelve irrational sums and differences are pairs of terms, the greater first, with one of six conditions: `BinomialTerms`, `FirstBimedialTerms`, `SecondBimedialTerms`, `MajorTerms`, `RationalMedialTerms` and `TwoMedialTerms` (10.36–10.41, 10.73–10.78). Their sum is a `Binomial`, a `FirstBimedial`, …, a `SideTwoMedials`; their difference an `Apotome`, a `FirstApotomeOfMedial`, …, a `MedialWholeWithMedial`. The six binomials and the six apotomes (Defs.~II and III) are the binomial terms with one of six further conditions, `FirstTerms ρ r x y`, …, `SixthTerms`, relative to a rational line $r$ laid out, with plus or minus. So the second half of the book shares its arguments with the first: the terms of 10.54–10.65 are lemmas (`proposition_54_terms`, …), applied in 10.91–10.102 to the difference; the terms carry over to commensurable lines in 10.66–10.70 and 10.103–10.107 alike; and 10.42–10.47 and 10.79–10.84 rest on the same fact, that a medial area does not exceed another by a rational one (10.26). The corollary to 10.111 is that no line is of two of the thirteen kinds, by Euclid's argument: the square on each, applied to a rational line, makes a breadth of a kind of its own.

Heiberg regards Prop.~10.10 and Props.~10.112–10.115 as interpolations; they are proved as given. Where Euclid takes numbers "not having the ratio of a square to a square" (10.10, 10.28–10.30, 10.48–10.53), the proofs take particular ones, $4$ and $3$, $16$ and $12$, $9$ and $7$, and show it by Prop.~8.24. Euclid lays down three rational lines commensurable in square only (10.28, 10.32) without saying how; they are found by 10.6's corollary. In 10.115 "not the same as any before" is read as incommensurable in square with each line before. Steps marked missed: the agreement of the two proportions of numbers, in 10.9 that ratios with the same squared ratio are the same, and in the second lemma after 10.28 that a number between consecutive squares is not square.

== What is checked, and what is assumed

Euclid often passes over small steps without comment. He says that two circles cut one another, or that a point falls inside an angle, because the figure shows it. In System E, such facts follow by a fixed set of diagrammatic, metric and transfer rules. The tactics `euclid_apply`, `euclid_assert` and `euclid_finish` find these small steps automatically. They apply the rules to the facts at hand, and to the facts so obtained, until the step follows or nothing new appears. Each rule they apply is recorded, so the result is an ordinary Lean proof of the step. When a gap is larger than that, the formal proof has to fill it explicitly. The comment `-- Missed by Euclid.` marks such places, where Euclid relied on a fact that he never proved.

One thing is taken on trust: the points, lines and circles of System E and its rules are _axioms_, as are Book 3's circumferences. They are not derived from a model of the plane, such as pairs of real numbers. Book 5 adds no axioms: the laws of magnitudes are the class `Magnitude`, so each proposition holds for every kind of magnitude that obeys them. Books 6–10 add none either. Everything else, every step, the order of the steps and the use of each proposition and rule, is checked by Lean. The proofs in this book were checked with Lean 4.36, using a version of System E taken from LeanEuclid and extended for this edition. The command `make check` in the source repository repeats the check.
