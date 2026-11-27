# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

A Typst port of Richard Fitzpatrick's LaTeX edition of Euclid's Elements (Greek Heiberg text + English translation, side by side). All thirteen books and the Greek–English lexicon are ported. The LaTeX text sources (`BookNN/BookN.tex`, `Book00/Introduction.tex`, `Book99/Lexicon.tex`) are kept as the reference and as input to `tools/`; never edit them. The LaTeX build and the EPS figures were removed (figures live on as SVG).

## Build

```sh
make                                     # ElementsGreekEnglish.pdf, ElementsEnglish.pdf, ElementsLean.pdf
make check                               # check the Lean proofs (slow; needs z3, cvc5, smt-portfolio)
make check BOOK=1                        # check one book's proofs
make cache                               # fetch prebuilt Mathlib (once, and after a Mathlib bump)
make clean
typst watch Elements.typ                 # rebuild on change (Greek-English)
typst compile --input greek=no Elements.typ ElementsEnglish.pdf
```

The English edition (`--input greek=no`) is made by the helpers in `functions.typ`: when `with-greek` is false, `parallel*` and `parallel-image` emit only the English column at full width, `running-header` centers the English title, and `Elements.typ` omits the Lexicon. Keep all Greek inside these helpers so both editions stay correct.

The Lean edition (`--input lean=yes`, which implies no Greek) is the Introduction, the primer `Book00/Lean.typ` and the books listed in `lean-books` in `functions.typ`, which also sets the title-page subtitle ("Books 1–3, with proofs…"). Each `Book01/PropNN.typ` ends with `#lean-proof("/lean/Elements/Book1/PropNN.lean")` after its `content-box`; the helper is a no-op in the other editions and otherwise typesets the `.lean` file (minus `import`/`namespace`/`end` lines) under a *Formalization* heading, highlighted by `lean/lean4.sublime-syntax`. The PDF build never runs Lean.

### Lean project (`lean/`)

- Lean 4.36 (`lean/lean-toolchain`) and Mathlib `v4.36.0` (`lean/lakefile.lean`), the only dependency. Bump them together; Mathlib tags match Lean versions.
- `lean/SystemE/` is System E from LeanEuclid commit `33a72c0` (MIT, `lean/LICENSE-LeanEuclid`), ported to 4.36, without UniGeo and the commented-out `Formalization` files. It is ours now: extend it here (e.g. tangency for Book 3).
- `lean/Smt/` is the part of lean-smt that SystemE uses (Apache 2.0, `lean/Smt/LICENSE`): SMT-LIB terms and commands, and `Smt.Solver`, which runs the external `smt-portfolio` (z3 + cvc5). `Data/Sexp.lean` and `Dsl/Sexp.lean` are upstream's 4.36 versions; the rest is from the 4.19 fork, ported.
- `lean/Elements/Book1/PropNN.lean` are LeanEuclid's `Book/PropNN.lean` with imports renamed to `Elements.Book1.PropNN`. Primed variants stay in their proposition's file. Each book has a root module `lean/Elements/BookN.lean` importing its propositions; `lean/Elements.lean` imports the roots.
- `lean/Elements/Book2/` are Book 2's proofs, written here in System E. Convention (top of `lean/Elements/Book2.lean`): rectangles and squares are products of lengths, as in Prop. 1.47, but proofs still build Euclid's figure and argue with areas. Lemmas proved from earlier propositions (`rectangle_on`, `parallel_between`) are in `lean/Elements/Book2/Lemmas.lean`, typeset after Book 2's definitions. Inside `namespace Elements.Book2`, cite Book 1's `proposition_N` by full name when Book 2 has its own `proposition_N`.
- Big figures (Prop. 2.8): every SystemE step sends the whole context to the solvers and first runs `simp_all` over it, so z3 or Lean can exhaust memory. Build the figure with `euclid_apply`, take the needed facts as named `have`/split `obtain` (named conjunctions get destructed by later steps), and close with a lemma over only those facts. `set_option systemE.simpAll false in` skips `simp_all` for one step. Never `maxHeartbeats 0`; run checks under `systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=0`.
- `make check` runs `lake build` in `lean/` (about 12 minutes from clean). Steps closed by SMT are admitted by SystemE's `SMT_VERIF` axiom, so a passing build trusts the solvers; a step the solvers can't close is a build error.
- Saturation is tried before the solvers on every step and gives kernel-checked proofs. Every axiom of `SystemE/Theory/Inferences/` (and lemmas proved from them) yields clauses: one per conclusion plus contrapositives. Small diagrammatic clauses fire forward to a fixpoint; metric ones fire on demand for the atoms of a metric goal; any clause is used backward on a goal literal (iterative deepening; shallow pass first, then recursive); metric literals go to `linarith only` over the nearest metric facts (equalities reduced to a spanning forest, `≠` split into `<`/`>`), but only when a native simplex finds a Farkas certificate, and then over just the facts it uses (Mathlib's `linarith` runs interpreted and is slow). Facts are indexed by statement and by each object argument; matching takes the literal with the fewest candidates first. Backward search goes to depth 3, at most 800 calls per literal. The diagrammatic closure is cached per declaration and extended incrementally on later steps; hypotheses that `simp_all` reintroduced are matched by type. Guarded lemmas (one metric premise, e.g. `between_of_lt`) fire forward when `linarith` proves that premise. Diagrammatic literals near the top are also proved by contradiction: assume the negation, saturate incrementally, look for a fact and its negation. Point inequalities can follow from lengths (`neByMetric`). The engine is `lean/SaturateCore.lean`, imports only `Lean` and is compiled natively (`precompileModules`; Lake loads `libelements_SaturateCore.so` as a plugin, `lake env lean` needs `--load-dynlib=.lake/build/lib/libelements_SaturateCore.so`). Its lemmas and the `linarith` call are in `lean/SystemE/Meta/Tactics/Saturate.lean`. Options: `systemE.saturate`, `systemE.saturateBudget`, `systemE.smt` (false: unproved steps are errors), `systemE.stats` (log each step's outcome). Iterate with `lake build SystemE` and `tools/gaps.sh`, not full builds.

There are no package dependencies and no tests; verify by compiling and inspecting the PDF (`pdftoppm -f N -l N -png` to look at a page).

## Structure

- `Elements.typ` — root: page/footer/paragraph setup, then `#include`s `Book00/Introduction.typ`, `BookNN/BookN.typ` for each book of the edition (`edition-books`), and `Book99/Lexicon.typ`.
- `functions.typ` — all shared layout helpers; every content file imports from it (`#import "../functions.typ": *`).
- `BookNN/BookN.typ` — book title, running header, then `#include`s `Definitions*.typ` (and in Book 1 `Postulates.typ`, `CommonNotions.typ`) and `PropNN.typ` (`PropNNN.typ` in Book 10) in order.

### Proposition file pattern

```typst
#content-box[
  #parallel-proposition(NN, note: [...])     // optional note on the heading
  #parallel([Greek], [English])              // one call per paragraph pair
  #parallel-image("/Book02/fig01", 2.2in)    // figure pair fig01g.svg / fig01e.svg
  #parallel-subheading([Πόρισμα.], [Corollary])
  ...
]
```

- Figures use `parallel-image` with SVGs converted from the original EPS figures (`greek: false` when only the English one exists).
- Each book's title page shows a colored frontispiece (`BookNN/front.svg`, 4.5in high), generated by `tools/fronts.py` in the style of Byrne's Euclid; the main title page shows `euclid.jpg`, a detail of Raphael's School of Athens (JPEG, embedded in the PDF as is).
- Definitions use `#parallel([Greek], [English], n: N)` for numbering.
- `content-box-note` puts footnotes at the bottom of the enclosing `content-box`, not the page. Book subtitles use plain `#footnote`.
- `running-header([Greek], [English])` is the page header of each book.
- `no-footer()` suppresses the page number on the current page; `chapter(alt, body)` emits a heading whose outline entry differs from the displayed text.

## Conventions

- Greek is Unicode NFC (precomposed polytonic), not italicized, no hyphenation. Ano teleia is U+0387, elision U+1FBF, numeral sign U+0374.
- English math labels are spaced, `$A B C$`, so Typst doesn't read `ABC` as a variable. Other math is Typst math (`sqrt(...)`, `k^(1 \/ 2)` — `\/` keeps a literal slash, `thin` for LaTeX `\,`).
- Citations use a non-breaking space: `[Prop.~1.4]`, `[Props.~6.1, 10.11]`, `[Def.~1.15]`, `[Post.~3]`, `[C.N.~1]`, with `corr.`/`lem.` suffixes.
- The English follows Fitzpatrick, keeping his parenthetical insertions, bracketed interpolations and literalisms that mirror the Greek; typos, wrong citations and label slips were corrected during the port.

## Tools (`tools/`)

- `tex2typ.py BOOK [--write] [--dump]` — converts `BookNN/BookN.tex` to Typst files. `--write` overwrites every file of that book, discarding manual edits made since; use `--dump` to inspect. Warnings like `paras 4/3` mean Greek and English paragraph counts differ and need a manual split.
- `greek.py` — transliteration (`\gr{...}` babel/teubner encoding) to Unicode Greek.
- `lex2typ.py` — converts `Book99/Lexicon.tex`.
- `fronts.py` — draws the book frontispieces `BookNN/front.svg` (Byrne-style flat colors; edit and rerun to change them).
- `gaps.sh BOOK [NN...]` — runs propositions with SMT off and lists the steps saturation can't close, each with the literal it got stuck on or "budget" (about a minute for Book 1, no solvers).
- `SmtFree.lean` — lists theorems free of `SMT_VERIF` (`cd lean && lake env lean ../tools/SmtFree.lean`, after `make check`).

## Repo notes

- `tmp/` is gitignored scratch space; so is `lean/.lake/`. `*.pdf` is ignored, so build output never gets committed.
