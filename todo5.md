# Milestone 5 — Book 5: tasks

Book 5 is Eudoxus's theory of proportion: 25 propositions about magnitudes, their equal multiples, and ratios. It has corollaries to 5.7 and 5.19. Nothing in it is a figure. Euclid's diagrams are straight lines that stand for magnitudes of any kind, so System E is not used.
- 5.1–5.6: multiples.
- 5.7–5.10: same and greater ratios.
- 5.11–5.15: ratios combined.
- 5.16–5.19: alternation, separation, composition, and the remainder.
- 5.20–5.25: ratios via equality (ex aequali), perturbed proportion, and the last two.

The tasks run in order. The common rules in [Roadmap.md](Roadmap.md) apply throughout.

## Routine for every task

- Each task ends with these steps:
  - `make check BOOK=5` and `make` pass;
  - `grep -r sorry lean/Elements/Book5` finds nothing;
  - commit, and remove the task from this file.
- A proposition's `lean/Elements/Book5/PropNN.lean` and its `#lean-proof(...)` line in `Book05/PropNN.typ` go in together.
- Inside `namespace Elements.Book5`, write `Elements.BookN.proposition_M` in full for other books' propositions.
- Keep Lean lines to 90 characters, so that they don't wrap in the PDF.
- Run every check under `systemd-run --user --scope -q -p MemoryMax=6G -p MemorySwapMax=0`. Never use `maxHeartbeats 0`; a finite limit is fine.

How Book 5 differs from Books 1–4:
- **Plain Lean.** The proofs are ordinary Lean with Mathlib tactics (`omega`, `linarith`, `simp`, `abel`), not `euclid_*`. Saturation and SMT play no part, and `tools/gaps.sh` does not apply. `tools/SmtFree.lean` must still list no Book 5 theorem with SMT.
- **Faithfulness.** Euclid proves facts about multiples (5.1–5.6) that Mathlib has as lemmas on `n • a` (`smul_add`, `add_smul`, `mul_smul`).
  - Don't cite those lemmas for a fact Euclid proves. Prove it his way, by induction on the multiple, and cite his proposition from then on.
  - Mathlib's lemmas may be used for what Euclid takes for granted: arithmetic of the counting numbers, and the algebra of addition (C.N. 1–5).
- **No reals, no division.** Ratios are not numbers. "A : B :: C : D" is Def. 5.5, over equimultiples. Don't define a ratio as `a / b`, which would make the book trivial.

## T5. Props. 5.16–5.19: alternation, separation, composition, the remainder

- **5.16:** alternation. All four magnitudes must be of one kind: the statement takes one type.
- **5.17:** separation. This is the second long proof, with many equimultiples.
- **5.18:** composition, by contradiction. It assumes a fourth proportional exists, per T1, and the step is marked.
- **5.19:** as whole to whole, so remainder to remainder. Uses 5.16 and 5.17.
  - The corollary (conversion) is `proposition_19_corollary`.
  - Euclid only says it is "clear, from this". Prove it from 5.17 and 5.19, and mark the steps he leaves out.

Risk: medium to high. Euclid's proof of 5.17 names eight magnitudes and four equimultiples. Split it into lemmas: one for the multiples, one for the comparisons.

## T6. Props. 5.20–5.25: ex aequali, perturbed proportion, and the last two

- **5.20–5.21:** the comparison lemmas for ex aequali, ordinary and perturbed. Uses 5.8, 5.10, 5.13, and 5.16 or 5.11.
- **5.22–5.23:** ex aequali, ordinary and perturbed.
  - 5.22 is for any number of magnitudes, per T1: induction on the chain, with Euclid's three-term case as its step.
  - 5.23 is for three, as Euclid states it.
- **5.24:** adding magnitudes with the same ratio to the same magnitude.
- **5.25:** in a proportion, the largest and the smallest together exceed the other two.

## T7. Magnitudes in the plane

The bridge to Book 6: instances of T1's class for magnitudes of System E.
- **Lengths:** segments of positive length, `|(a─b)|` with `a ≠ b`, as a type with addition and order.
  - Addition needs a segment equal to the sum: `extend_point_longer` and Prop. 1.3 give one.
  - The instance may use the reals of System E's `|(a─b)|` underneath. The point is that Book 6 can take ratios of lengths with Book 5's propositions.
- **Areas:** triangle and parallelogram areas, positive.
- **Archimedes:** for lengths and areas it follows from the reals underneath. Say so in the doc comment: it is a fact of the model, not one Euclid proves.
- Decide whether the carrier is the positive reals that occur as lengths, or all positive reals. Choose whatever Book 6 needs. Write down the decision, and its effect on Book 6, in `Roadmap.md` under Milestone 6.

Risk: medium. If an instance needs more than System E gives, stop and write down what is missing. Don't add axioms.

## T8. Primer and docs

- **`Book00/Lean.typ`:** a section on Book 5:
  - magnitudes and their class, and multiples;
  - Defs. 5.4, 5.5, 5.7 as written in Lean;
  - why there are no reals or division;
  - the assumption of 5.18;
  - how "any number of magnitudes" is written.
- **Typesetting:** typeset `Magnitude.lean` (and any `Lemmas.lean`) after Book 5's definitions, as Books 2–4 do. Update the Lean edition's subtitle, which comes from `lean-books`, if needed.
- **`CLAUDE.md`:** the Book 5 notes: plain Lean, Mathlib's `nsmul` lemmas not used for Euclid's facts, and where the class is. Change "Books 1–4 are SMT-free" to what holds now.
- **`Roadmap.md`:** delete Milestone 5, and add T7's decisions to Milestone 6.
- **README:** Books 1–5.

## T9. Final check

- `make check` from clean, all books, under the cap. Note the time.
- `tools/gaps.sh N` for N = 1–4: no failing steps. `tools/SmtFree.lean`: no theorem with SMT.
- `grep -r sorry lean/Elements lean/SystemE` finds nothing.
- Inspect `ElementsLean.pdf`:
  - the subtitle "Books 1–5";
  - Book 5's title page and the class;
  - the longest proofs (5.8, 5.17);
  - the corollaries to 5.7 and 5.19.
- `ElementsEnglish.pdf` and `ElementsGreekEnglish.pdf` are unchanged.
- Commit and push.
