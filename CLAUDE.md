# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

A Typst port of Richard Fitzpatrick's LaTeX edition of Euclid's Elements (Greek Heiberg text + English translation, side by side), all thirteen books and the Greek–English lexicon, plus Lean proofs of Books 1–2. The LaTeX sources (`BookNN/BookN.tex`, `Book00/Introduction.tex`, `Book99/Lexicon.tex`) are kept as reference and as input to `tools/`; never edit them.

## Build

```sh
make                       # ElementsGreekEnglish.pdf, ElementsEnglish.pdf, ElementsLean.pdf
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
#lean-proof("/lean/Elements/Book1/PropNN.lean")   // Books 1–2; no-op outside the Lean edition
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
- Books 1 and 2 are SMT-free: every step is closed by saturation and checked by the kernel. Keep them so. Check with `tools/gaps.sh N` (no failing steps; run `Lemmas.lean` directly) and `tools/SmtFree.lean` (none with SMT).
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
