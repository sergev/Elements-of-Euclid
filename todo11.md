# Milestone 11 — Book 11: tasks

Book 11 is the first book of solid geometry: 39 propositions, 28 definitions, one lemma (after 11.23) and two corollaries (11.33, 11.35).
- 11.1–11.3: lines and planes. Fitzpatrick's note: Euclid's proofs are not rigorous, and these three are properly additional axioms.
- 11.4–11.19: perpendiculars to planes, parallel lines in space, parallel planes, perpendicular planes.
- 11.20–11.23, 11.26: solid angles.
- 11.24–11.34: parallelepipeds: equal, cut, in ratio as their bases, similar (cubed ratio), reciprocal.
- 11.35–11.39: a lemma for 11.36, solids from three proportionals, similar solids in proportion, the cube's diameter, prisms.

The tasks run in order. The common rules in [Roadmap.md](Roadmap.md) apply throughout, and so does Milestone 11 there.

T1 ends with a design note for the user to review. Stop there: no proofs until the user has approved it.

## Routine for every task

- Each task ends with these steps:
  - `make check BOOK=11` and `make` pass;
  - `grep -r sorry lean/Elements/Book11` finds nothing;
  - `tools/gaps.sh 11` finds no failing steps, and `tools/SmtFree.lean` lists no Book 11 theorem with SMT;
  - commit, and remove the task from this file.
- The files are `lean/Elements/Book11/PropNN.lean`, two digits. The theorems are `proposition_1`, …, `proposition_39`, with `proposition_23_lemma`, `proposition_33_corollary`, `proposition_35_corollary`.
- A proposition's Lean file and its `#lean-proof(...)` line in `Book11/PropNN.typ` go in together.
- Inside `namespace Elements.Book11`, write `Elements.BookN.proposition_M` in full for other books' propositions.
- Keep Lean lines to 90 characters, so that they don't wrap in the PDF.
- Run every check under `systemd-run --user --scope -q -p MemoryMax=6G -p MemorySwapMax=0`. Never use `maxHeartbeats 0`; a finite limit is fine.
- Large figures (11.23, 11.29–11.31, 11.35, 11.38): build the figure in a lemma, and argue in lemmas that take only the facts they need, as Book 4 does.

How Book 11 differs from the books before it:
- **Space, not the plane.** System E is one plane, with global sorts `Point`, `Line`, `Circle`. Book 11 needs points, lines and planes in space, and it cites Books 1 and 6 for figures that lie in any plane (1.4, 1.8 and 1.26 for triangles in space, 6.2 in 11.17, 1.35 and 6.14 in 11.31).
- **New axioms.** This is the first book since Book 3 to need them. They go in `lean/Elements/Book11/Axioms.lean`, each true in ℝ³, and the primer lists them all.
- **Solids as magnitudes.** From 11.25 on, solids are equal, added, and in ratio (Def. 5.5 in 11.25, cubed ratio in 11.33). A volume is a Book 5 magnitude, so Book 5 is cited as Lean terms, as Books 6 and 10 do.

## T1. Design note (stop for review)

Write the design note as the header comment of `lean/Elements/Book11.lean` (not yet imported anywhere), commit it, and give the user a summary. Settle these choices, with the reasons:
- **Sorts.** Points, lines and planes of space, with names that don't clash with System E's global `Point` and `Line` (say `Space.Point`, `Space.Line`, `Plane`, or a namespace). Incidence (`onLine`, `onPlane`), betweenness, and length and angle in space.
- **Incidence axioms.** Hilbert's spatial axioms I.4–I.8: three non-collinear points determine one plane; a line with two points in a plane lies in it; two planes with a common point have another; four points not in a plane exist. Decide how 11.1–11.3 relate to them. Following Fitzpatrick's note, they may be stated as theorems that cite the axioms rather than Euclid's argument, with a doc comment saying so; or Euclid's argument is followed where it can be made to work.
- **The plane's geometry in every plane.** Following the Roadmap: an axiom that each plane carries System E's plane, by a map from System E's `Point` onto the plane's points that preserves betweenness, lines, length, angle and area. Then a triangle in space lies in a plane (11.2), is pulled back to System E, Book 1 or Book 6 is applied there, and the result is pushed forward. Write the transport lemmas (a figure of k points in a plane, pulled back) so that each citation of Book 1 is one step. Check that saturation closes the plane steps after the pull-back. Steps in space are Lean terms that cite the axioms and the propositions, as Book 5 and Book 10 do.
- **Definitions.** Def. 11.3 (a line at right angles to a plane: to every line in the plane through its foot), Def. 11.4 (planes at right angles), Def. 11.8 (parallel planes do not meet), parallel lines in space (in one plane and not meeting, Fitzpatrick's note to 11.6), the solid angle of three plane angles (Def. 11.11, for 11.20–11.23, 11.26), the parallelepiped (six faces in three pairs of parallel planes), its height, and the prism (Def. 11.13, for 11.28 and 11.39). Defs. 11.5–11.7 (inclinations) and 11.14–11.28 (sphere, cone, cylinder, the regular solids) are not used in Book 11. Leave them to Books 12 and 13, and say so.
- **Volume.** Choose between:
  - `volume` of a tetrahedron as the primitive, with axioms like System E's area of a triangle (zero for four points in a plane, symmetric in the vertices, additive when a tetrahedron is split at a point on an edge or a face, equal for equal and similar tetrahedra). Solids are then sums of tetrahedra, as figures are sums of triangles in Books 1, 2 and 6, and Book 12's pyramids are the same sort. The parallelepiped is a fixed sum of tetrahedra, and a cut by a plane (11.25, 11.28) must be shown to be additive.
  - `volume` of a parallelepiped and of a prism, with axioms for the cuts Euclid makes.

  Recommended: the first, since Book 12 is about pyramids. Def. 11.10 ("equal and similar") is how Euclid shows solids equal (11.25, 11.28, 11.31); say whether it becomes the congruence axiom for tetrahedra or a lemma built from it. Fitzpatrick's notes to 11.34 (equal solids on equal bases have equal heights) and 11.37 (equal ratios have equal cubed ratios) name steps Euclid takes for granted; they are proved and marked `-- Missed by Euclid.`. A volume is a positive real (`Volume`, next to `Length` and `Area` in `Elements/Book5/Plane.lean`), so it is a Book 5 magnitude.
- **The model.** Check every axiom against ℝ³ in the note, one line each. Proving them in Mathlib's `EuclideanSpace ℝ (Fin 3)` is not required, but if it is cheap for the incidence axioms, it is worth doing in `tmp/` as a check.
- **Statements to try.** Before writing the note, write in scratch (`tmp/`, with `sorry`, not committed) the statements of 11.1, 11.4, 11.6, 11.11, 11.17, 11.20, 11.23, 11.25, 11.29, 11.31, 11.33, 11.35 and 11.39, and check that the sorts and definitions carry them. Put three of them in the note as examples.

Stop after the note. The user reviews it, and T2 starts only after that.

Risk: high. Every later task depends on these choices, and a wrong axiom is not caught by the kernel.

## T2. Axioms, definitions and scaffolding

- `lean/Elements/Book11/Axioms.lean`: the axioms approved in T1, each with a doc comment naming what Euclid assumes (Hilbert's axiom, or the definition it stands for).
- `lean/Elements/Book11/Definitions.lean`: Defs. 11.3, 11.4, 11.8, 11.10–11.13 and the parallelepiped, each with its number. Put `@[simp] abbrev`s where saturation should see through them, as in Books 3, 4 and 6.
- `lean/Elements/Book11/Lemmas.lean`: the transport lemmas (pull back a triangle, a quadrilateral, a figure of k points in a plane), and the facts of the model for volume if T1 chose some.
- Typeset `Axioms.lean` and `Definitions.lean` after `#include "Definitions.typ"` in `Book11/Book11.typ`, with `#lean-proof(..., title: [...])`. Any page break goes in the Lean edition only.
- `lean/Elements/Book11.lean` with the header comment of T1, imported in `lean/Elements.lean`. Add `11` to `lean-books` in `functions.typ`; the subtitle becomes "Books 1–11". Check that `ElementsEnglish.pdf` and `ElementsGreekEnglish.pdf` don't change (compare their `pdftotext` output). Add the Book 11 names to `lean/lean4.sublime-syntax`.
- Prove one Book 1 citation in space end to end (1.4 for two triangles in different planes) as a test of the transport, before going on.

Risk: high.

## T3. Props. 11.1–11.10: lines, planes, perpendiculars, parallels

- **11.1–11.3:** a straight line is not partly in a plane and partly above it; two lines that cut one another are in one plane, and so is every triangle; the common section of two planes is a line. As decided in T1; Fitzpatrick's note goes in the doc comment of 11.1.
- **11.4, 11.5:** a line at right angles to two lines at their point of section is at right angles to their plane (through 1.4, 1.8, 1.15, 1.26 in two different planes); three lines at right angles to one line at a point are in one plane.
- **11.6–11.10:** two lines at right angles to one plane are parallel; a line joining points on two parallels is in their plane; a parallel to a perpendicular is perpendicular; parallels to one line, not in one plane with it, are parallel; angles with parallel sides are equal (through 1.33, 1.8).

Risk: medium. 11.4 is the template for every later use of Def. 11.3; most of its steps are Book 1 in some plane, so it shows whether the transport is cheap enough.

## T4. Props. 11.11–11.19: perpendiculars and planes

- **11.11, 11.12:** to draw the perpendicular from a point to a plane, and to set one up at a point of a plane. Constructions, `∃` with the properties, like Book 1's.
- **11.13:** only one such perpendicular at a point, on one side. "On the same side" of a plane needs a definition, or an axiom for the two sides of a plane (as Hilbert's plane separation); T1 should have settled it.
- **11.14–11.16:** planes perpendicular to one line are parallel; planes through lines parallel to two cutting lines are parallel; parallel planes cut by a plane have parallel common sections.
- **11.17:** lines cut by parallel planes are cut in the same ratios (6.2 in two planes, then 5.11). Ratios are Book 6's `p ∶ q ∷ r ∶ s` over lengths in space, or Book 5's `Proportion` over `Length`; T1 decides.
- **11.18, 11.19:** planes through a perpendicular are perpendicular to the plane (Def. 11.4); the common section of two planes perpendicular to a plane is perpendicular to it.

Risk: medium.

## T5. Props. 11.20–11.23, 11.26: solid angles

- **11.20, 11.21:** in a solid angle of three plane angles any two are greater than the third (1.20, 1.25, 1.4); the three are less than four right angles (1.32, 11.20). Fitzpatrick's note: 11.21 is proved only for three plane angles. State it for three, as Euclid proves it, and say so in the doc comment; a version for any number needs a convex base polygon, and is not required.
- **11.22, 11.23:** a triangle from the chords of three plane angles of equal sides; to construct a solid angle from three plane angles satisfying 11.20 and 11.21. 11.23 is the longest proof of the book (1.47, 3.31, 4.1, 4.5, 5.14, 5.16, 6.2, 6.4, 11.12), with its lemma (that the side found is greater than the radius). Split the figure as T1 says for large figures.
- **11.26:** to construct at a point of a line a solid angle equal to a given one. "Equal solid angles" needs a definition (by the three plane angles, equal and in the same order); T1 should have settled it.

Risk: high for 11.23.

## T6. Props. 11.24, 11.25, 11.27, 11.28: parallelepipeds

- **11.24:** a solid contained by parallel planes has opposite faces equal parallelograms (11.10, 11.16, 1.34).
- **11.25:** a parallelepiped cut by a plane parallel to two opposite faces is to the parts as base to base. Euclid's proof is Def. 5.5 with equimultiples of the solids, laid side by side and equal by Def. 11.10; follow it, as 6.1 does in Book 6.
- **11.27:** to describe on a line a parallelepiped similar to a given one (11.26, 6.12, 5.22). Similar solids are Def. 11.9.
- **11.28:** a parallelepiped cut by the plane through diagonals of opposite faces is halved (Def. 11.10 for the two prisms, 1.34).

Risk: high. The first use of volume: the additivity of cuts by a plane must be in place.

## T7. Props. 11.29–11.34: equal and proportional parallelepipeds

- **11.29, 11.30:** parallelepipeds on the same base with the same height are equal, with the upper ends on the same lines (11.29, by prisms and subtraction, 1.36) and not (11.30, through 11.29 twice).
- **11.31, 11.32:** on equal bases with the same height they are equal (the longest of these: 1.23, 1.35, 6.14, 5.7, 5.9, 5.11, 11.25, 11.29, 11.30); with the same height they are as their bases (1.45, 11.25, 11.31).
- **11.33:** similar parallelepipeds are in the cubed ratio of corresponding sides (Def. 5.10; Book 8's `CubedRatio` is for numbers, so define the cubed ratio for magnitudes as Book 5's continued proportion of four), with the corollary (as the first to the fourth of four lines in continued proportion).
- **11.34:** equal parallelepipeds have bases reciprocally proportional to heights, and conversely. Fitzpatrick's note names two steps Euclid takes for granted; prove them and mark them missed.

Risk: high for 11.29–11.31.

## T8. Props. 11.35–11.39

- **11.35:** equal plane angles with raised lines making equal angles: the perpendiculars from equal points make equal angles with the raised lines (1.26, 1.4, 1.47, 1.48, 1.8, 11.8), with the corollary (equal raised lines have equal perpendiculars).
- **11.36:** the parallelepiped on three proportional lines equals the equilateral one on the mean, equiangular to it (6.14, 11.26, 11.31, 11.35).
- **11.37:** four proportional lines and similar parallelepipeds on them. Fitzpatrick's note: equal ratios have equal cubed ratios, and conversely; prove it from Book 5 and mark it missed.
- **11.38:** in a cube, the common section of the planes through the midpoints of opposite faces' sides and the diameter bisect one another (1.4, 1.14, 1.15, 1.26, 1.29, 1.33, 11.9). The cube is Def. 11.25; it is needed here only as a parallelepiped with equal edges at right angles.
- **11.39:** prisms of equal height on a parallelogram and on a triangle half of it are equal (1.34, 11.28, 11.31).

Risk: medium.

## T9. Primer and docs

- **`Book00/Lean.typ`:** a section on Book 11:
  - the sorts of space and how they sit beside System E's plane;
  - every axiom of `Axioms.lean`, with what Euclid assumes in its place, and Fitzpatrick's note on 11.1–11.3;
  - the transport of a figure in a plane to System E, and what saturation does and doesn't do in Book 11;
  - volume as a magnitude, and Def. 11.10;
  - the steps marked missed (11.34, 11.37), and what is not formalized (Defs. 11.5–11.7, 11.14–11.28, 11.21 for more than three angles).
- **`CLAUDE.md`:** Book 11 notes: sorts, axioms, transport, definitions and where they are, volume. Update "Books 1–10".
- **`Roadmap.md`:** delete Milestone 11, and update the table and the opening paragraph. Record in Milestones 12 and 13 what they inherit: the sorts and axioms of space, the transport, volume (Book 12's pyramids, prisms, 12.3–12.9), 11.28 and 11.39 (12.3, 12.4), 11.33 (12.8, 12.12), and Defs. 11.14–11.28 left for them.
- **README:** Books 1–11.

## T10. Final check

- `make check` from a clean build (remove `lean/.lake/build` only), all books, under the cap. Note the time (Book 10's was 3m12s).
- `tools/gaps.sh N` for N = 1–4, 6 and 11: no failing steps. `tools/SmtFree.lean`: no theorem with SMT.
- `grep -r sorry lean/Elements lean/SystemE` finds nothing.
- Every axiom in `lean/Elements/Book11/Axioms.lean` is in the primer, and `#print axioms` for 11.39 shows no others.
- `ElementsEnglish.pdf` and `ElementsGreekEnglish.pdf` unchanged; the Lean PDF's subtitle reads "Books 1–11"; inspect its Book 11 pages.
- Commit, and delete this file.
