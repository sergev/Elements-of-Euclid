# Milestone 3 — Book 3: tasks

Book 3 has 37 propositions (corollaries to 3.1 and 3.16), on circles: chords, tangents, angles in segments, arcs, and the power of a point.

The tasks run in order. The common rules in [Roadmap.md](Roadmap.md) apply throughout.

## Routine for every task

- Each task ends with `make check BOOK=3` and `make` passing, then a commit and removal of the task from this file.
- A proposition's `lean/Elements/Book3/PropNN.lean` and its `#lean-proof(...)` line in `Book03/PropNN.typ` go in together.
- Inside `namespace Elements.Book3`, write `Elements.Book1.proposition_N` or `Elements.Book2.proposition_N` in full whenever Book 3 has its own `proposition_N`.

Running checks:
- Run every check under `systemd-run --user --scope -q -p MemoryMax=6G -p MemorySwapMax=0`. Never use `maxHeartbeats 0`; a finite limit is fine.
- Keep the file being checked closed in VS Code, whose Lean server runs its own uncapped solvers.

When the solvers struggle:
- **Big figures:** build the figure with `euclid_apply`, then take the needed facts as named `have`s or as split `obtain`s. Close with a lemma over only those facts (see Prop. 2.8).
- **Segment orientation:** when a goal compares products of the same segments written in different orders (`|(a─b)|` against `|(b─a)|`), add the symmetric step as an assert.
- **`simp_all`:** if it blows up, turn it off for that step with `set_option systemE.simpAll false in`.

## T6. Props. 3.14–3.16: chords and the line at the end of a diameter

- **3.14–3.15:** equal chords are equally far from the center; the diameter is the greatest chord, and a nearer chord is greater. These use Prop. 1.47 with products.
- **3.16:** the perpendicular at the end of a diameter falls outside the circle (a tangent). No other straight line fits between it and the circle.
  - **The horn angle:** Euclid's further claim is about the curved angle between circle and tangent, and System E has no curved angles. State and prove the straight-line parts. Write a comment saying what is left out; T13 adds a note to the primer.
- **Corollary:** the perpendicular at the end of a diameter touches the circle (T1).

## T7. Props. 3.17–3.19: tangents

- **3.17:** draw a tangent from a given point. This is a construction: `∃` a line touching the circle.
- **3.18:** the radius to the point of contact is perpendicular to the tangent.
- **3.19:** the perpendicular to a tangent at the point of contact passes through the center.

## T8. Props. 3.20–3.22: angles in segments

First, define the segment of a circle (Def. 3.6) and the angle in a segment (Def. 3.8), in `lean/SystemE/Book3.lean` or as hypotheses. A segment is a chord `ab` with the points of the circle on one side of line `ab`.

- **3.20:** the angle at the center is double the angle at the circumference.
  - Euclid proves one position of the figure and leaves the other ("let it be bent").
  - Prove the cases he treats, and mark any case the statement then has to assume.
- **3.21:** angles in the same segment are equal.
- **3.22:** the opposite angles of a quadrilateral in a circle sum to two right angles.

## T9. Props. 3.23–3.25: similar segments

- **Def. 3.11:** similar segments admit equal angles. Define it with T8's angle in a segment.
- **3.23–3.24:** similar segments on the same, or equal, straight lines are equal. Euclid moves one segment onto the other.
  - System E's `superposition` handles triangles only, so decide how to state "the segments coincide" before proving these.
  - If it needs a new rule, discuss it first.
- **3.25:** complete the circle of a given segment (a construction).

Risk: high. Write a short design note before any proof.

## T10. Props. 3.26–3.30: circumferences (arcs)

Euclid's "equal circumferences" have no counterpart in System E.

- **Design note first.** Write a short note on how to state arcs, reviewed before any proof. Choose between:
  - an arc as two endpoints plus the side of their chord, with "equal circumferences" defined from the angles standing on them;
  - a new primitive (an arc's size) with rules, which means new axioms.

  The first keeps everything inside System E, but risks making 3.26–3.27 restate their own definition.
- **3.26–3.29:** in equal circles, equal angles stand on equal circumferences, and conversely; equal chords cut off equal circumferences, and conversely.
- **3.30:** bisect a given circumference.

Risk: high.

## T11. Props. 3.31–3.34: semicircle, tangent and chord, segment on an angle

- **3.31:** the angle in a semicircle is right; in a greater segment it's less than right, and in a lesser segment greater. The horn-angle clauses (angle of the segment) are left out, as in 3.16.
- **3.32:** the angle between tangent and chord equals the angle in the alternate segment.
- **3.33:** construct, on a given straight line, a segment admitting a given angle.
- **3.34:** cut off from a given circle a segment admitting a given angle.

Uses T1 and T8.

## T12. Props. 3.35–3.37: the power of a point

These use products, as in Book 2.
- **3.35:** for two intersecting chords, the rectangles on their pieces are equal. Uses Props. 2.5 and 1.47.
- **3.36:** for a secant and a tangent from an outside point, the rectangle on the secant and its outer part equals the square on the tangent. Uses Prop. 2.6.
- **3.37:** the converse of 3.36.

Expect the Book 2 orientation asserts.

## T13. Primer and docs

- **`Book00/Lean.typ`:**
  - the Book 3 definitions (touching, segments, arcs);
  - the decisions from T9 and T10;
  - a note on what is left out: the horn angles in 3.16 and 3.31.
- **Typeset any `lean/Elements/Book3/Lemmas.lean`** after Book 3's definitions, as in Book 2.
- **`CLAUDE.md`:** the Book 3 notes. **`Roadmap.md`:** Milestone 3 done.

## T14. Final check

- `make check` from clean, all books, under the cap. Note the time.
- `grep -r sorry lean/` finds nothing.
- Inspect `ElementsLean.pdf`:
  - the subtitle;
  - Book 3's title page and lemmas;
  - the longest proofs;
  - the corollaries to 3.1 and 3.16.
- `ElementsEnglish.pdf` and `ElementsGreekEnglish.pdf` are unchanged.
- Update the README, commit and push.
