# Roadmap: Lean proofs for Books 5–13

Books 1–4 are done (Milestones 1–4): Book 1's 48 propositions from LeanEuclid and Books 2, 3 and 4 (14, 37 and 16) written here, all in System E, typeset in `ElementsLean.pdf` and checked by `make check`. This file plans the remaining books, one milestone per book, numbered to match: Milestone N is Book N. A book depends on the books before it, so the milestones run in sequence. Only Milestones 7–9 (Books 7–9) can be done in parallel with the geometry.

## Common rules for every milestone

- **Files.** Proofs go in `lean/Elements/BookN/PropNN.lean`, in namespace `Elements.BookN`, as `proposition_NN`. The book's root module `lean/Elements/BookN.lean` imports them, and `lean/Elements.lean` imports the root. Lemmas and corollaries get their own names: `proposition_NN_lemma` and `proposition_NN_corollary`. Primed variants stay in the proposition's file.
- **Typesetting.** Each `BookNN/PropNN.typ` gets `#lean-proof(...)` after its `content-box`. Adding the book's number to `lean-books` in `functions.typ` puts it in the Lean edition and in the title-page subtitle.
- **Faithfulness.** The statement says what Euclid says, and the proof follows his steps, citing the same propositions. Steps he leaves out are proved and marked `-- Missed by Euclid.` His proofs are not to be replaced with a shorter modern one.
- **Trust.** No `sorry`. New axioms are allowed only for what Euclid assumes (his definitions and postulates, or System E's rules). They live in one file per book, `lean/Elements/BookN/Axioms.lean`, and the primer lists them.
- **Definitions.** A book's definitions are formalized where they are used, as Lean `def`s with the Euclid number in a doc comment. They are not typeset separately unless that turns out useful.
- **Done.** `make check` passes (`make check BOOK=N` checks one book while working on it). `make` builds the PDF with the book included, and its pages have been inspected. The primer (`Book00/Lean.typ`) covers any new notation.
- **System E.** It is our own copy in `lean/SystemE/`. New relations or rules a book needs go there, in files named for the book that introduces them. Lemmas proved from earlier propositions, such as repeated constructions, go in `lean/Elements/BookN/Lemmas.lean`.
- **Toolchain.** Lean 4.36 and Mathlib v4.36. Upgrade Lean and Mathlib together, between milestones, not during one.

## Milestone 5 — Book 5: proportion (25 propositions)

Eudoxus's theory of ratios of magnitudes: equimultiples (Def. 5.5), alternation, composition, separation, ex aequali.

- **Basis.** Not System E. Formalize magnitudes abstractly, as an ordered additive structure with the Archimedean property (Def. 5.4). Define "A : B :: C : D" by Def. 5.5 over equimultiples `m • A`, `n • B`, and prove the propositions from that. Avoid reals and division, which would make the book trivial.
- **New.** A `Magnitude` class, `Proportion` (5.5), `GreaterRatio` (5.7), and an instance for segment lengths and areas in E. That instance connects the book to Book 6.
- **Risk.** Medium. The proofs are algebraic, not diagrammatic; SMT is of no help, and they are ordinary Lean. Euclid's 5.18 has a known gap (existence of a fourth proportional); mark it `-- Missed by Euclid.` and prove it, or state it as the assumption he makes.

## Milestone 6 — Book 6: similar figures (33 propositions)

6.1 (triangles of equal height are as their bases), 6.2 (parallels cut sides proportionally), similar triangles (6.4–6.8), mean proportionals, application of areas (6.27–6.29), 6.31 (generalized 1.47), 6.33 (angles at the center are as arcs).

- **Basis.** System E plus Book 5 proportion, through the Milestone 5 instance for lengths and areas.
- **New.** Similar rectilinear figures (Def. 6.1), reciprocally proportional figures, duplicate ratio (Def. 5.9 used here). Areas of general rectilinear figures as sums of triangles.
- **Risk.** High. 6.1 is the bridge between geometry and Book 5, and its proof by equimultiples needs constructing m copies of a segment for arbitrary m. That requires induction, which is outside E's style. 6.27–6.29 are long. 6.33 needs Book 3's arcs.

## Milestone 7 — Book 7: numbers (39 propositions)

The Euclidean algorithm (7.1–7.2), proportion of numbers, primes, relatively prime numbers, least common multiple.

- **Basis.** Mathlib's `ℕ`, not System E. A "number" is a multitude of units, so `n ≥ 2` and the unit is separate. "A measures B" is `A ∣ B`, and "parts" are proper fractions of a number. Define proportion of numbers by Def. 7.20, and do not use Book 5's. Books 8 and 9 build on this basis.
- **New.** Definitions for 7.Def.1–23 (part, parts, prime, relatively prime, plane and solid numbers, perfect). The proofs follow Euclid's subtractive algorithm and avoid Mathlib's ready-made `Nat.gcd` theorems except where Euclid has already proved the fact.
- **Risk.** Low. Each step is easy for Lean. It can run in parallel with Milestones 3–6, since only 7.Def.20 comes near Book 5 and it is defined separately.

## Milestone 8 — Book 8: continued proportions (27 propositions)

Numbers in continued proportion, mean proportionals between numbers, square and cube numbers.

- **Basis.** Milestone 7.
- **New.** Continued proportion of a sequence of numbers. Euclid's "let there be any multitude of numbers A, B, C…" means lists of arbitrary length; use `List ℕ` or `Fin n → ℕ`, and choose once for Books 8 and 9.
- **Risk.** Low to medium. The arbitrary-length sequences need induction, where Euclid argues with three or four named numbers and "similarly".

## Milestone 9 — Book 9: primes and series (36 propositions)

Uniqueness of prime factors (9.14), infinitude of primes (9.20), odd and even numbers (9.21–9.34), sums of geometric series (9.35), perfect numbers (9.36).

- **Basis.** Milestones 7 and 8.
- **New.** Odd and even numbers as Euclid defines them (7.Def.6–10), and the sum of a sequence for 9.35–9.36.
- **Risk.** Low to medium, for the same reason as Book 8.

## Milestone 10 — Book 10: incommensurable magnitudes (115 propositions)

10.1 (the basis of exhaustion), commensurability, the irrationality of √2 type results, and the classification of the 13 kinds of irrational lines (binomials, apotomes, medials …).

- **Basis.** Segment lengths as positive reals with Book 5's ratios linked to `ℝ` division, plus Mathlib's `Irrational`. Commensurable means the ratio is rational. "Rational" in Euclid's sense is commensurable with a chosen line, in length or in square; define it so, not as `ℚ`.
- **New.** The 13 kinds of irrational lines as definitions over `ℝ`; the lemmas Euclid needs (10.28 lemmas, Pythagorean triples).
- **Risk.** High, due to size. It is the longest book, at about a quarter of the Elements, and highly repetitive: 10.36–10.72 and 10.73–10.110 mirror each other. Split it into sub-milestones of about 25 propositions each. Make proofs of the mirrored propositions share lemmas. The connection to geometry (lines and squares on them) depends on Milestone 6.

## Milestone 11 — Book 11: solid geometry (39 propositions)

Lines and planes in space, perpendiculars to planes, parallel planes, solid angles, parallelepipeds.

- **Basis.** System E is planar, so it cannot be used. Choose between:
  - a three-dimensional extension in E's style: sorts `Point`, `Line`, `Plane`, with axioms for incidence, betweenness and perpendicularity. This is faithful but a research project.
  - Mathlib's `EuclideanSpace ℝ (Fin 3)` with affine subspaces. This is solid ground, but proofs are analytic and look nothing like Euclid's.

  Recommended: the first, with axioms kept small and grounded in Hilbert's spatial axioms, and Book 1's plane results available in each plane by an axiom that a plane carries a System E model.
- **New.** All of the above. This milestone starts with a design note, reviewed before any proofs are written.
- **Risk.** High. No existing formalization of Euclid's solid geometry in this style is known. SMT automation from LeanEuclid will not apply without new translation work.

## Milestone 12 — Book 12: the method of exhaustion (18 propositions)

Circles are to one another as the squares on their diameters (12.2), and the volumes of pyramids, cones, cylinders and spheres (12.18).

- **Basis.** Milestone 11's solid geometry, Book 5's proportion, and 10.1. Areas and volumes of curved figures need a notion of magnitude beyond triangle sums: axioms for area and volume as additive and monotone, in the spirit of Book 5 magnitudes, rather than Mathlib's measure theory.
- **New.** Area of a circle and volume of a solid as magnitudes, inscribed polygons and polyhedra approximating them.
- **Risk.** High. The double reductio of exhaustion proofs (12.2, 12.5, 12.10–12.12, 12.18) is the hardest logic in the Elements to state faithfully.

## Milestone 13 — Book 13: the regular solids (18 propositions)

The golden section (13.1–13.6), pentagon and decagon side relations (13.7–13.12), the construction of the five regular solids in a sphere (13.13–13.17), and their comparison (13.18). The closing claim that there are no other regular solids gets a separate theorem.

- **Basis.** Milestones 4, 10 and 11. 13.1–13.12 are planar, so they can start once Book 10's binomial and apotome definitions exist (13.6, 13.11 use them).
- **New.** Regular polyhedra inscribed in a sphere, described by their vertices; an icosahedron and dodecahedron are 12 and 20 points.
- **Risk.** High for 13.16–13.17 (icosahedron, dodecahedron): many points and many solid-geometry steps.

## Order and size

| Milestone | Book | Props | Basis | Risk |
|---|---|---|---|---|
| 1 | 1 | 48 | System E | done |
| 3 | 3 | 37 | System E + tangency | medium |
| 4 | 4 | 16 | System E | medium |
| 5 | 5 | 25 | abstract magnitudes | medium |
| 6 | 6 | 33 | E + Book 5 | high |
| 7 | 7 | 39 | Mathlib `ℕ` | low, can run in parallel |
| 8 | 8 | 27 | Book 7 | low–medium |
| 9 | 9 | 36 | Books 7–8 | low–medium |
| 10 | 10 | 115 | `ℝ` + Book 5 | high (size) |
| 11 | 11 | 39 | new solid system | high |
| 12 | 12 | 18 | Book 11 + magnitudes | high |
| 13 | 13 | 18 | Books 4, 10, 11 | high |

Milestones 3–4 finish the plane geometry that System E was built for, so they should go first. Milestones 7–9 can start any time. Milestones 11–13 depend on the design decision in Milestone 11 and should not start until Books 2–6 have shown how far E's style stretches.
