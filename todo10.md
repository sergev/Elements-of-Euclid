# Milestone 10 — Book 10: tasks

Book 10 is the longest book: 115 propositions, with lemmas (after 10.13, 10.16, 10.21, 10.28 (two), 10.32, 10.41, 10.53, 10.59) and corollaries (10.3, 10.4, 10.6, 10.9, 10.23, 10.111, 10.114). It has three groups of definitions: Defs. 10.1–10.4 (commensurable, in square, rational), Defs. II (the six binomials, before 10.48) and Defs. III (the six apotomes, before 10.85).
- 10.1–10.8: exhaustion, the process of 10.2, greatest common measures, ratios of numbers.
- 10.9–10.16: squares on lines, and the calculus of commensurability.
- 10.17–10.26: application of areas; rational and medial rectangles.
- 10.27–10.35: lines to be found, and Pythagorean triples (10.28 lemmas).
- 10.36–10.72: the six irrational sums (binomial, bimedials, major, …), the six binomials, and how they correspond.
- 10.73–10.110: the same for differences (apotome, apotomes of a medial, minor, …), the six apotomes.
- 10.111–10.115: apotome and binomial are not the same; their product; infinitely many irrationals.

The tasks run in order. The common rules in [Roadmap.md](Roadmap.md) apply throughout, and so does Milestone 10 there.

## Routine for every task

- Each task ends with these steps:
  - `make check BOOK=10` and `make` pass;
  - `grep -r sorry lean/Elements/Book10` finds nothing;
  - commit, and remove the task from this file.
- Book 10's Typst files have three digits, `Book10/Prop001.typ`; so do the Lean files, `lean/Elements/Book10/Prop001.lean`, so that they sort. The theorems are `proposition_1`, …, `proposition_115`; lemmas `proposition_13_lemma`, `proposition_28_lemma_1`, `_2`; corollaries `proposition_3_corollary`.
- A proposition's Lean file and its `#lean-proof(...)` line in `Book10/PropNNN.typ` go in together.
- Inside `namespace Elements.Book10`, write `Elements.BookN.proposition_M` in full for other books' propositions.
- Keep Lean lines to 90 characters, so that they don't wrap in the PDF.
- Run every check under `systemd-run --user --scope -q -p MemoryMax=6G -p MemorySwapMax=0`. Never use `maxHeartbeats 0`; a finite limit is fine.
- Mirrored propositions share lemmas: 10.73–10.110 follow 10.36–10.72 with minus for plus. Write the shared part once, over the pair of terms, and apply it to the sum and to the difference. Where a proof is "the same as 10.N", the doc comment says so.

How Book 10 differs from the books before it:
- **Plain Lean over Book 5's magnitudes.** No System E, no saturation. Ratios are Book 5's `Proportion` (Def. 5.5), with Book 5's propositions cited as Lean terms, as Book 6 does. No division of magnitudes; never Mathlib's `Irrational`, `ℚ`, or `Real.sqrt` in a statement or a step Euclid takes.
- **Two layers.**
  - 10.1–10.8 and 10.11–10.13, 10.15, 10.16 are about any magnitudes: state them for `[Magnitude M]`, as Book 5 does.
  - From 10.9 on, the magnitudes are lines and areas: `Length` and `Area` (`Elements/Book5/Plane.lean`, positive reals). The square on a line and the rectangle contained by two lines are areas, products of lengths, as in Book 2.
- **Numbers.** "The ratio which a number has to a number" joins Book 5's proportion with Books 7–9's numbers (`ℕ`, Def. 7.20). 10.5–10.9 make the bridge; after that, Book 7–9 propositions are cited as Lean terms (8.24, 8.26, 9.1, 9.2 for squares).
- **Irrational means Euclid's irrational.** Rational and irrational are relative to an assigned line `ρ` (Def. 10.3), and a line is rational when commensurable with `ρ` in length or in square only. Incommensurability is proved as Euclid proves it, from the hypotheses (10.13, 10.16 and so on), not from the irrationality of a real number.

## T8. Props. 10.60–10.72: squares applied; same order

- **10.60–10.65:** the square on each irrational sum, applied to a rational line, makes the binomial of the same order as breadth. The converses of 10.54–10.59.
- **10.66–10.70:** a line commensurable in length with each kind is of the same kind and order. Through 10.13, 10.15, 10.23.
- **10.71, 10.72:** a rational and a medial area, or two incommensurable medial areas, added together: the square root is one of four (two) irrational sums. Case analyses; keep Euclid's cases.

Risk: medium.

## T9. Props. 10.73–10.90: the six differences, and the six apotomes

- **10.73–10.78:** the difference of the terms of each kind is irrational (apotome, first and second apotome of a medial, minor, that which with a rational area makes a medial whole, that which with a medial area makes a medial whole). Mirror 10.36–10.41, through the lemmas of T6.
- **10.79–10.84:** only one line can be attached to each (the uniqueness of 10.42–10.47 with minus). Fitzpatrick notes 10.82 is 10.45 with minus signs.
- **10.85–10.90:** to find the first to sixth apotome. Fitzpatrick's footnotes to 10.48, 10.50, 10.53 apply.

Risk: medium, if T6's lemmas are over the terms; high otherwise.

## T10. Props. 10.91–10.110: apotomes and areas

- **10.91–10.96:** the square root of a rectangle of a rational line and an apotome of order k is the k-th difference (mirror of 10.54–10.59).
- **10.97–10.102:** the square on each difference, applied to a rational line, makes the apotome of the same order (mirror of 10.60–10.65).
- **10.103–10.107:** commensurable with each kind is of the same kind and order (mirror of 10.66–10.70).
- **10.108–10.110:** a medial taken from a rational area, a rational from a medial, a medial from a medial: the square roots of the remainders (mirror of 10.71, 10.72).

Risk: medium.

## T11. Props. 10.111–10.115: binomial and apotome

- **10.111:** an apotome is not the same as a binomial, with the corollary listing the thirteen irrational lines, all different from one another. State the corollary as: no line is of two of the thirteen kinds (or as Euclid has it, the kinds are different), with a doc comment on what is and is not proved.
- **10.112–10.114:** the square on a rational line applied to a binomial makes an apotome with commensurable terms in the same ratio, and conversely; an apotome and a binomial with such terms contain a rational area (with corollary). Heiberg considers 10.112–10.115 early interpolations; prove them as given.
- **10.115:** from a medial line arise infinitely many irrational lines, none the same as any before. State it with a sequence: `x 0` medial, `x (n + 1)` the mean proportional of `ρ` and `x n`, and each `x (n + 1)` incommensurable in square with every `x i`, `i ≤ n`, and irrational. Say in the doc comment how "not the same" is read.

Risk: medium.

## T12. Primer and docs

- **`Book00/Lean.typ`:** a section on Book 10:
  - commensurable, in square, rational and medial, and the choices of T1 (numbers as magnitudes, lines and areas as products, the assigned line `ρ`);
  - the construction lemmas from Books 2 and 6 and why they are facts of the model;
  - the twelve irrationals as pairs of terms with plus or minus, and the six binomials and apotomes;
  - 10.1 and 10.2 as the first infinite processes; the interpolations (10.10, 10.112–10.115) and the steps marked missed.
- **`CLAUDE.md`:** Book 10 notes: the definitions and where they are, the two layers, the shared lemmas for the mirrored halves, file names with three digits. Update "Books 1–9".
- **`Roadmap.md`:** delete Milestone 10, and update the table and the opening paragraph. Record in Milestones 12 and 13 what they inherit: 10.1 for exhaustion (12.2, 12.5, 12.10–12.12, 12.18), and the binomial and apotome definitions for 13.6, 13.11, 13.17, 13.18.
- **README:** Books 1–10.

## T13. Final check

- `make check` from a clean build (remove `lean/.lake/build` only), all books, under the cap. Note the time (Book 9's was 2m28s).
- `tools/gaps.sh N` for N = 1–4 and 6: no failing steps. `tools/SmtFree.lean`: no theorem with SMT.
- `grep -r sorry lean/Elements lean/SystemE` finds nothing.
- `grep -rn "Irrational\|ℚ\|Real.sqrt\|Rat\." lean/Elements/Book10`: each hit is in a model lemma with a comment, or none.
- Inspect `LeanElementsOfEuclid.pdf`:
  - the subtitle "Books 1–10";
  - Book 10's title page and the three definition pages with their Lean definitions;
  - 10.1, 10.2, 10.9, 10.17, 10.36, 10.42, 10.54, 10.73, 10.111 and 10.115.
- `ElementsEnglish.pdf` and `ElementsGreekEnglish.pdf` are unchanged.
- Delete this file, and commit.
