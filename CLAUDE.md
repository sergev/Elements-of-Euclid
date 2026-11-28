# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

A Typst port of Richard Fitzpatrick's LaTeX edition of Euclid's Elements (Greek Heiberg text + English translation, side by side), all thirteen books and the Greek–English lexicon, plus Lean proofs of Books 1–10. The LaTeX sources (`BookNN/BookN.tex`, `Book00/Introduction.tex`, `Book99/Lexicon.tex`) are kept as reference and as input to `tools/`; never edit them.

## Build

```sh
make                       # ElementsGreekEnglish.pdf, ElementsEnglish.pdf, LeanElementsOfEuclid.pdf
make check                 # check the Lean proofs (needs z3, cvc5, smt-portfolio)
make check BOOK=1          # one book
make cache                 # fetch prebuilt Mathlib (once, and after a Mathlib bump)
typst watch Elements.typ   # rebuild on change
```

There are no tests; verify by compiling and inspecting the PDF (`pdftoppm -f N -l N -png`).

Editions: `--input greek=no` (English only) and `--input lean=yes` (Introduction, the primer `Book00/Lean.typ`, and the books in `lean-books` in `functions.typ`, each proposition followed by its Lean file). Both are made by the helpers in `functions.typ`; keep all Greek inside them. The PDF build never runs Lean.

## Structure

- `Elements.typ` — root; includes `Book00/Introduction.typ`, `BookNN/BookN.typ`, `Book99/Lexicon.typ`.
- `functions.typ` — all shared layout helpers; every content file imports it.
- `BookNN/BookN.typ` — title, running header, then includes definitions and `PropNN.typ` in order.

Proposition file pattern:

```typst
#content-box[
  #parallel-proposition(NN, note: [...])     // optional note on the heading
  #parallel([Greek], [English])              // one call per paragraph pair
  #parallel-image("/Book02/fig01", 2.2in)    // figure pair fig01g.svg / fig01e.svg
  #parallel-subheading([Πόρισμα.], [Corollary])
]
#lean-proof("/lean/Elements/Book1/PropNN.lean")   // Books 1–10; no-op outside the Lean edition
```

Definitions use `#parallel([Greek], [English], n: N)`. `content-box-note` puts footnotes at the bottom of the box.

## Conventions

- Greek is Unicode NFC (precomposed polytonic), not italicized, no hyphenation. Ano teleia is U+0387.
- English math labels are spaced, `$A B C$`, so Typst doesn't read `ABC` as a variable.
- Citations use a non-breaking space: `[Prop.~1.4]`, `[Def.~1.15]`, `[Post.~3]`, `[C.N.~1]`.
- The English follows Fitzpatrick, keeping his insertions and literalisms.

## Lean (`lean/`)

- Lean 4.36 and Mathlib `v4.36.0`; bump them together.
- `SystemE/` is System E from LeanEuclid (MIT), ported; it is ours to extend. `Smt/` is the part of lean-smt it uses.
- `Elements/BookN/PropNN.lean`, with a root `Elements/BookN.lean` per book. Variants and helper lemmas stay in their proposition's file; derive weaker variants from stronger ones rather than repeating a construction. Book 2: rectangles and squares are products of lengths, but proofs build Euclid's figure and argue with areas; shared lemmas are in `Elements/Book2/Lemmas.lean`.
- Book 3: its definitions (touching, segments, similar segments) are `@[simp] abbrev`s in `SystemE/Book3.lean`, over System E's relations, so saturation sees through them; `intersectsCircle` means *cuts*. Circumferences are the opaque `α.arc b c s` (away from `s`) with the axioms in `Elements/Book3/Axioms.lean`; no other new axioms. Facts with `∀` (internal/external touching) are not used by saturation: instantiate them, `‹∀ x, …› p`.
- Book 4: figures are vertices in order with their sides' lines, convex; the definitions are `@[simp] abbrev`s in `SystemE/Book4.lean`, written out per number of sides (`pentagon`, `inscribedPentagon`, `circumscribedPentagon`, …). Lemmas from the figure (tangents meeting, feet of perpendiculars, order of points on a circle) are in `Elements/Book4/Lemmas.lean`. Big figures: build them in a lemma, and argue in lemmas that take only the facts they need, applied once per vertex or side with the labels rotated.
- Book 5 is plain Lean, not System E. The class `Magnitude` and Defs. 5.4, 5.5, 5.7 (`Proportion`, `GreaterRatio`) are in `Elements/Book5/Magnitude.lean`; multiples `n • a` with `n : ℕ+` are our own, and Mathlib's `nsmul` lemmas are never used for what Euclid proves (5.1–5.6 by induction, cited from then on). Ratios are not numbers: no reals, no division. "Any number" is `Fin (n + 1) → M`. The fourth proportional of 5.18 is a hypothesis. `Elements/Book5/Plane.lean`: `Length`, `Area` (positive reals) for Book 6.
- Book 6: two kinds of step. Geometric steps are System E's, closed by saturation; steps about ratios cite Book 5 as Lean terms (saturation ignores ratios). Ratios in the figure are `p ∶ q ∷ r ∶ s` over `Figure`s (`(a─b)`, `△a:b:c`, `□a:b:c:d`, `⬠a:b:c:d:e`; for 6.33 angles `∡a:b:c` and circumferences `⌒α:b:c:s`), with `size`, `mag`, and the Book 5 wrappers (`inv`, `trans`, `alt`, `exAequali`, `eq_left`) in `Elements/Book6/Definitions.lean` and `Lemmas.lean`; geometric definitions (`□`, `⬠`, equiangular figures) are `@[simp] abbrev`s in `SystemE/Book6.lean`, Def. 6.1 (`similarTriangles`, …) in `Definitions.lean`. Facts of the model (`Positive.fourth`, `Positive.mult_val`, `Length.fourth`) only where Euclid has no argument, with a comment (6.31's area fourth proportional); fourth proportionals of lines come from Prop. 6.12. `area_linarith` (`Elements/Book6/Tactics.lean`) closes area sums over triangles named in any vertex order. `euclid_apply` splits every conjunction in context, so build similarity hypotheses just before use. 6.33 takes multiples of angles and circumferences past the circle as reals: `Wound` counts the semicircles passed and compares the remainders by Props. 3.26, 3.27; no new axioms.
- Book 7 is plain Lean over `ℕ`, like Book 5: no System E, no saturation. A number is `1 < a`, the unit `1`; `a * b` is `a` taken `b` times ("`b` multiplies `a`", Def. 7.15), and "measures" is `∣`. Definitions (`PartOf`, `PartsOf`, Def. 7.20 `a ∶ b ∷ c ∶ d` with a fourth case for a greater first, `PrimeTo`, `PrimeNumber`, `Least`, `SameRatio₃`, …) in `Elements/Book7/Definitions.lean`; the common notions, `proportion_iff`, the process `remainder` of 7.1–7.2, and Book 5's 5.7, 5.9, 5.11, 5.13 for numbers (from the model `proportion_iff_cross`, marked missed) in `Lemmas.lean`. Mathlib only for what Euclid takes for granted: never `Nat.gcd`, `Nat.Coprime`, `Nat.Prime`, `Nat.lcm`; no `mul_comm`/`ring` before 7.16, cited with a comment after; associativity marked missed. No division.
- Book 8 is plain Lean over `ℕ` on Book 7's basis, with Book 7's Mathlib rule. Any multitude is `Fin (n + 1) → ℕ`; `Definitions.lean` has `ContinuedIn a r s` (each to the next as `r` to `s`), `Continued`, `SameRatios`, `LeastSeq` (Book 7's `Least` for a sequence), `FallBetween n a b`, and Defs. 5.9, 5.10, 6.5 for numbers (`SquaredRatio`, `CubedRatio`, `CompoundRatio`, middle terms between the two numbers). `Lemmas.lean`: ex aequali along a sequence (`SameRatios.extremes`), `LeastSeq.eq`, and `three`/`four` for three or four numbers. Euclid's "similarly" is induction (`Fin.induction`, `Fin.lastCases`), stated for any multitude: 8.2's numbers are `powers a b n` (Prop02), 8.4 adds a ratio at a time. Squares and cubes are `a * a`, `a * a * a`, never `^`. Sides and least terms may be the unit, so 8.20, 8.21, 8.26, 8.27 state sides with `0 <`, not `PlaneNumber`/`SimilarPlane`. Mathlib here is built only for what is imported: no `Fin.snoc`, `![…]`, `linarith`.
- Book 9 is plain Lean over `ℕ` on Books 7 and 8, with Book 7's Mathlib rule (also never `Even`, `Odd`, `Nat.Perfect`, `Nat.divisors`). `Definitions.lean`: `EvenNumber` (`a = h + h`), `OddNumber` (not even; the unit is odd), `EvenTimesEven`/`EvenTimesOdd`/`OddTimesOdd` (`a = e * f`, the odd factors greater than the unit), `LeastMeasuredSeq c a` (7.36 for any multitude). `Lemmas.lean`: `odd_iff` (Def. 7.7's second reading), `exists_leastMeasuredSeq` and `.measures`, `unit_proportion`, `continued_ratio` (same ratio any number of steps apart), "from a unit" (`Continued a`, `a 0 = 1`: `unit_succ`, `unit_two`, `unit_one_lt`, `unit_pos`, `fin_one_eq`), `sum_add`, `sum_excess`, `sum_powers_two`, and `sum_parts` (parts of a number as a list of distinct numbers, for Def. 7.22). Statements from a unit are by index, `a ⟨2 * k, _⟩`; 9.11's corollary `a j = a i * a (j - i)`; 9.13: every number measuring `a n` is some `a i`. Doubled from the unit is `powers 1 2 n`.
- Book 10 is plain Lean over Book 5's magnitudes, like Book 5: no System E, no saturation; Book 5 cited as Lean terms. Files have three digits, `Book10/Prop001.typ`, `Elements/Book10/Prop001.lean`. Two layers: 10.1–10.8, 10.11–10.13, 10.15, 10.16 for `[Magnitude M]` (division into equal parts is the hypothesis `Divisible M`, true of `Length`, `Area`); from 10.9 on, `Length` and `Area`, with `sq a`, `rect a b` (products). `Definitions.lean`: `Measures`, `Commensurable` (Def. 10.1), `CommensurableInSquare`, `InSquareOnly`, `Rational ρ x` (in length or in square), `RationalArea`, `MedialArea`, `Medial`, and `Number` (`ℕ+` as a magnitude, `(m : Number)`; Book 5's proportion of numbers is Def. 7.20 by `number_proportion_iff`). `Definitions2.lean`: the six term conditions (`BinomialTerms`, `FirstBimedialTerms`, `SecondBimedialTerms`, `MajorTerms`, `RationalMedialTerms`, `TwoMedialTerms`, greater first), the six sums (`Binomial`, …, `SideTwoMedials`), `ExceedsComm`/`ExceedsIncomm`, and Defs. II (`FirstTerms ρ r x y`, …, `SixthTerms`, relative to a rational `r`; `FirstBinomial ρ r l`, …). `Definitions3.lean`: the six differences (`l + y = x`: `Apotome`, …, `MedialWholeWithMedial`) and Defs. III (`FirstApotome`, …). `Lemmas.lean`: the commensurability basics and the model (class `Model`, `proportion_iff_mul`): Books 2 and 6 as model lemmas naming their propositions (6.1 `rect_proportion`, 6.22 `proportion_sq`, 2.4 `sq_add`, 2.7 `sq_add_sq_of_sub`, …) and the constructions (`Length.part`, `.cut`, `.fourth'`, `.mean`, `.exceeds`, `.hypotenuse`, `.semicircle`, `Area.side`, `.apply`, `.apply_short`, `.apply_excess`); no other model facts, no `Irrational`, `ℚ`, `Real.sqrt` outside the model. Rational calculus (`Rational.of_comm`, `.sq_rational`, `RationalArea.of_comm`, …) is in `Prop019.lean`. Mirrored halves share lemmas over the terms: `proposition_5N_terms` (10.54–10.59 for 10.91–10.96), `proposition_6N_terms` (10.60–10.65 for 10.97–10.102), `Transfers` with `.sum`/`.diff` (10.66–10.70, 10.103–10.107), `rational_add_medial_eq`, `medial_add_medial_eq`/`medial_sub_medial_eq` (10.42–10.47, 10.79–10.84). `OrderTerms ρ r k` (orders as `Fin 6`) and `LineKind` (the thirteen) are in `Prop111.lean`.
- Books 1–6 are SMT-free: every System E step is closed by saturation and checked by the kernel. Keep them so. Check with `tools/gaps.sh N` (no failing steps; run `Lemmas.lean` directly) and `tools/SmtFree.lean` (none with SMT).
- Saturation is tried before the solvers on every step. The engine is `SaturateCore.lean`, compiled natively and loaded as a plugin (`lake env lean --load-dynlib=.lake/build/lib/libelements_SaturateCore.so`); its lemmas are in `SystemE/Meta/Tactics/Saturate.lean`. Options: `systemE.smt` (false: unproved steps are errors), `systemE.stats` (log each step). Iterate with `lake build SystemE` and `tools/gaps.sh`, not full builds.
- When a step won't saturate, supply the fact Euclid takes from the figure as an explicit step: `equal_angles` (angle along a ray), `right_angle_on_lines` (right angle on the opposite ray), `sum_angles_onlyif`/`sum_areas_if`, `between_if`, `parallel_between`, `triple_incidence_1`/`_2`, circle intersections via points inside. Case-split disjunctions with `rcases`. `capped` means the declaration's budget is spent: raise `maxHeartbeats` to a finite value. `budget` over few facts: close with an explicit term or a lemma with only the needed hypotheses.
- Never `maxHeartbeats 0`. Run checks under `systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=0`.

## Tools (`tools/`)

- `tex2typ.py BOOK [--write] [--dump]` — converts `BookNN/BookN.tex` to Typst; `--write` overwrites the book's files.
- `greek.py`, `lex2typ.py` — transliteration to Unicode Greek; the lexicon.
- `fronts.py` — draws the Byrne-style frontispieces `BookNN/front.svg`.
- `gaps.sh BOOK [NN...]` — lists the steps saturation can't close, with SMT off.
- `SmtFree.lean` — lists theorems free of `SMT_VERIF` (`cd lean && lake env lean ../tools/SmtFree.lean`).

`tmp/` is gitignored scratch space; build output (`*.pdf`, `lean/.lake/`) is ignored too.
