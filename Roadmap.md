# Roadmap: Lean proofs for Books 11–13

Books 1–10 are done (Milestones 1–10): Book 1's 48 propositions from LeanEuclid and Books 2, 3 and 4 (14, 37 and 16) written here in System E, Book 5's 25 in plain Lean over a class of magnitudes, Book 6's 33 in System E with Book 5's proportion, Books 7, 8 and 9 (39, 27 and 36) in plain Lean over `ℕ`, and Book 10's 115 in plain Lean over Book 5's magnitudes, lines and areas, typeset in `LeanElementsOfEuclid.pdf` and checked by `make check`. This file plans the remaining books, one milestone per book, numbered to match: Milestone N is Book N. A book depends on the books before it, so the milestones run in sequence.

## Common rules for every milestone

- **Files.** Proofs go in `lean/Elements/BookN/PropNN.lean`, in namespace `Elements.BookN`, as `proposition_NN`. The book's root module `lean/Elements/BookN.lean` imports them, and `lean/Elements.lean` imports the root. Lemmas and corollaries get their own names: `proposition_NN_lemma` and `proposition_NN_corollary`. Primed variants stay in the proposition's file.
- **Typesetting.** Each `BookNN/PropNN.typ` gets `#lean-proof(...)` after its `content-box`. Adding the book's number to `lean-books` in `functions.typ` puts it in the Lean edition and in the title-page subtitle.
- **Faithfulness.** The statement says what Euclid says, and the proof follows his steps, citing the same propositions. Steps he leaves out are proved and marked `-- Missed by Euclid.` His proofs are not to be replaced with a shorter modern one.
- **Trust.** No `sorry`. New axioms are allowed only for what Euclid assumes (his definitions and postulates, or System E's rules). They live in one file per book, `lean/Elements/BookN/Axioms.lean`, and the primer lists them.
- **Definitions.** A book's definitions are formalized where they are used, as Lean `def`s with the Euclid number in a doc comment. They are not typeset separately unless that turns out useful.
- **Done.** `make check` passes (`make check BOOK=N` checks one book while working on it). `make` builds the PDF with the book included, and its pages have been inspected. The primer (`Book00/Lean.typ`) covers any new notation.
- **System E.** It is our own copy in `lean/SystemE/`. New relations or rules a book needs go there, in files named for the book that introduces them. Lemmas proved from earlier propositions, such as repeated constructions, go in `lean/Elements/BookN/Lemmas.lean`.
- **Toolchain.** Lean 4.36 and Mathlib v4.36. Upgrade Lean and Mathlib together, between milestones, not during one.

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
- **Left by Book 10.** 10.1 is `Elements.Book10.proposition_1` over `[Magnitude M]`: a sequence `x : ℕ → M` of remainders, from each more than half taken (`proposition_1'` for halves), some remainder less than a given magnitude. It is what 12.2, 12.5, 12.10–12.12 and 12.18 cite for exhaustion; their areas and volumes need only be a kind of magnitude.
- **New.** Area of a circle and volume of a solid as magnitudes, inscribed polygons and polyhedra approximating them.
- **Risk.** High. The double reductio of exhaustion proofs (12.2, 12.5, 12.10–12.12, 12.18) is the hardest logic in the Elements to state faithfully.

## Milestone 13 — Book 13: the regular solids (18 propositions)

The golden section (13.1–13.6), pentagon and decagon side relations (13.7–13.12), the construction of the five regular solids in a sphere (13.13–13.17), and their comparison (13.18). The closing claim that there are no other regular solids gets a separate theorem.

- **Basis.** Milestones 4, 10 and 11. 13.1–13.12 are planar, so they can start now.
- **Left by Book 10.** Lines are `Length`, with `sq`, `rect`, and rational relative to an assigned `ρ` (`Rational ρ x`, `RationalArea`, `Medial`). 13.6 (the cut in extreme and mean ratio of a rational line is an apotome) uses `Apotome ρ l` and `FirstApotome ρ r l` (`Definitions3.lean`); 13.11 (the side of a pentagon in a circle with a rational diameter is minor) uses `Minor ρ l`; 13.17, 13.18 use the same. The lines of Book 13's figures are System E segments, so `Length.of a b h` (`Elements/Book5/Plane.lean`) connects them, as Book 6 does. 10.111's corollary (`LineKind`) gives that the kinds differ.
- **New.** Regular polyhedra inscribed in a sphere, described by their vertices; an icosahedron and dodecahedron are 12 and 20 points.
- **Risk.** High for 13.16–13.17 (icosahedron, dodecahedron): many points and many solid-geometry steps.

## Order and size

| Milestone | Book | Props | Basis | Risk |
|---|---|---|---|---|
| 1 | 1 | 48 | System E | done |
| 3 | 3 | 37 | System E + tangency | medium |
| 4 | 4 | 16 | System E | medium |
| 5 | 5 | 25 | abstract magnitudes | medium |
| 6 | 6 | 33 | E + Book 5 | done |
| 7 | 7 | 39 | Mathlib `ℕ` | done |
| 8 | 8 | 27 | Book 7 | done |
| 9 | 9 | 36 | Books 7–8 | done |
| 10 | 10 | 115 | Book 5 + model of lines | done |
| 11 | 11 | 39 | new solid system | high |
| 12 | 12 | 18 | Book 11 + magnitudes | high |
| 13 | 13 | 18 | Books 4, 10, 11 | high |

Milestones 3–4 finish the plane geometry that System E was built for, so they should go first. Milestones 11–13 depend on the design decision in Milestone 11 and should not start until Books 2–6 have shown how far E's style stretches.
