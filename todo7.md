# Milestone 7 — Book 7: tasks

Book 7 is the first book on numbers: 39 propositions, with a corollary to 7.2.
- 7.1–7.3: the Euclidean algorithm, the greatest common measure.
- 7.4–7.10: part and parts.
- 7.11–7.15: proportion of numbers: remainders, sums, alternation, via equality, the unit.
- 7.16–7.19: multiplication: commutativity, products in the ratio of their factors, cross-multiplication.
- 7.20–7.22: the least numbers in a ratio.
- 7.23–7.28: numbers prime to one another.
- 7.29–7.32: prime numbers.
- 7.33–7.39: least numbers in given ratios, the least common multiple, parts.

The tasks run in order. The common rules in [Roadmap.md](Roadmap.md) apply throughout, and so does Milestone 7 there.

## Routine for every task

- Each task ends with these steps:
  - `make check BOOK=7` and `make` pass;
  - `grep -r sorry lean/Elements/Book7` finds nothing;
  - commit, and remove the task from this file.
- A proposition's `lean/Elements/Book7/PropNN.lean` and its `#lean-proof(...)` line in `Book07/PropNN.typ` go in together.
- Inside `namespace Elements.Book7`, write `Elements.BookN.proposition_M` in full for other books' propositions.
- Keep Lean lines to 90 characters, so that they don't wrap in the PDF.
- Run every check under `systemd-run --user --scope -q -p MemoryMax=6G -p MemorySwapMax=0`. Never use `maxHeartbeats 0`; a finite limit is fine.

How Book 7 differs from Books 1–6:
- **Plain Lean over `ℕ`, as Book 5 is over magnitudes.** No System E, no saturation, no SMT: `tools/gaps.sh` does not apply. Proofs are Lean terms and ordinary tactics.
- **Mathlib only for what Euclid takes for granted.** Linear facts about addition and order (`omega`, `linarith`) are his common notions. What Book 7 proves is never taken from Mathlib:
  - the algorithm and the greatest common measure (`Nat.gcd` and its lemmas);
  - the laws of multiplication, until he proves them (`mul_comm` is 7.16; `ring` uses it);
  - cross-multiplication (7.19);
  - `Nat.Coprime`, `Nat.Prime`, `Nat.lcm` and their lemmas (7.23–7.39).
  
  Once a proposition is proved, cite it, or a tactic that does the same, with a comment naming the proposition.
- **No division, no rationals.** A ratio of numbers is never `a / b`, in `ℕ` or `ℚ`.

## T9. Props. 7.33–7.39: least numbers, least common multiple, parts

- **7.33:** to find the least numbers in the ratio of any given numbers.
  - The construction divides by the greatest common measure: by 7.3 for three numbers, as in Euclid's figure. State it for three, or for any number if T1's "any multitude" makes that no harder.
  - The step that cites Prop. 5.13 uses T1's number version.
- **7.34:** to find the least number measured by two numbers, with Euclid's two cases (prime to one another or not).
- **7.35:** a number measured by two numbers is measured by the least one they measure.
- **7.36:** the least number measured by three numbers.
- **7.37, 7.38:** a number measured by a number has a part called the same as it, and conversely.
- **7.39:** to find the least number that has given parts.

Constructions ("to find") are stated as existence with the property, as in Book 6, plus "least" where Euclid proves it. Don't use `Nat.lcm`.

## T10. Primer and docs

- **`Book00/Lean.typ`:** a section on Book 7:
  - numbers over `ℕ`, the unit, and Def. 7.15's multiplication;
  - part, parts, and proportion by Def. 7.20, and why it is not Book 5's;
  - what is taken from Mathlib, and from which proposition on;
  - the gaps marked `Missed by Euclid`: the Book 5 citations, associativity, the common notions.
- **`CLAUDE.md`:** Book 7 notes: the basis, the rule about Mathlib, where the definitions are. Update "Books 1–6".
- **`Roadmap.md`:** delete Milestone 7. Record in Milestone 8 the choices Books 8 and 9 inherit: the "any multitude" representation, the definitions of similar plane and solid numbers, square and cube.
- **README:** Books 1–7.

## T11. Final check

- `make check` from a clean build, all books, under the cap. Note the time.
- `tools/gaps.sh N` for N = 1–4 and 6: no failing steps, since Book 7 must not disturb the geometry. `tools/SmtFree.lean`: no theorem with SMT.
- `grep -r sorry lean/Elements lean/SystemE` finds nothing.
- `grep -rn "Nat.gcd\|Nat.lcm\|Nat.Coprime\|Nat.Prime\|ring\b" lean/Elements/Book7`: each hit is allowed by the rule above, with a comment.
- Inspect `LeanElementsOfEuclid.pdf`:
  - the subtitle "Books 1–7";
  - Book 7's title page, definitions and lemmas;
  - the algorithm (7.1, 7.2), 7.20 and 7.31;
  - the corollary to 7.2.
- `ElementsEnglish.pdf` and `ElementsGreekEnglish.pdf` are unchanged.
- Commit and push.
