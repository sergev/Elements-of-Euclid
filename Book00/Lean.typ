#import "../functions.typ": chapter, no-footer

#chapter([Reading the Lean Proofs], [READING THE LEAN PROOFS])

#v(1em)

This edition gives each proposition of the books it contains twice. First comes Euclid's text in Richard Fitzpatrick's translation, then a formal version written in Lean 4, a programming language and proof assistant. Each proposition's formal statement and proof is printed after the English, under the heading _Formalization_. The proofs of Book 1 come from LeanEuclid, by L. Murphy, K. Yang, J. Sun, Z. Li, A. Anandkumar and X. Si, "Autoformalizing Euclidean Geometry", ICML 2024, distributed under the MIT license. The proofs of Book 2 were written for this edition, in the same system.

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

== What is checked, and what is assumed

Euclid often passes over small steps without comment. He says that two circles cut one another, or that a point falls inside an angle, because the figure shows it. In System E, such facts follow by a fixed set of diagrammatic, metric and transfer rules. The tactics `euclid_apply`, `euclid_assert` and `euclid_finish` find these small steps automatically. They translate the current facts into a query for the SMT solvers Z3 and CVC5, which search for a derivation. When a gap is larger than that, the formal proof has to fill it explicitly. The comment `-- Missed by Euclid.` marks such places, where Euclid relied on a fact that he never proved.

Two things are taken on trust. First, the points, lines and circles of System E and its rules are _axioms_. They are not derived from a model of the plane, such as pairs of real numbers. Second, when a solver reports that a step follows, Lean accepts that report through an axiom and does not rebuild the step as a Lean proof. Everything else, the order of the steps and the use of each proposition and rule, is checked by Lean. The proofs in this book were checked with Lean 4.36, using LeanEuclid's implementation of System E. The command `make check` in the source repository repeats the check.
