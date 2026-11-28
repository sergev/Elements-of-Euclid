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
