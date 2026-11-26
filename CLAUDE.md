# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

A Typst port of Richard Fitzpatrick's LaTeX edition of Euclid's Elements (Greek Heiberg text + English translation, side by side). All thirteen books and the Greek–English lexicon are ported. The original LaTeX sources (`Elements.tex`, `BookNN/BookN.tex`, `BookNN/fig*{e,g}.eps`) are kept in the tree as the reference; never edit them.

## Build

```sh
make                                     # typst compile -> ElementsTypst.pdf
make clean
typst watch ElementsTypst.typ            # rebuild on change
```

CeTZ (`@preview/cetz:0.4.2`) is fetched automatically by Typst. There are no tests; verify by compiling and inspecting the PDF (`pdftoppm -f N -l N -png` to look at a page). The LaTeX build (`latex Elements`) is legacy.

## Structure

- `ElementsTypst.typ` — root: page/footer/paragraph setup, then `#include`s `Book00/Introduction.typ`, `BookNN/BookN.typ` for Books 1–13, and `Book99/Lexicon.typ`.
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

- Books 2–13 use `parallel-image` with SVGs converted from the EPS figures (`greek: false` when only the English EPS exists). Book 1 Props 1–12 instead draw figures in CeTZ via `parallel-fig(figNN)`, called twice with letter maps from `greek-map`; labels must go through `letters.at("X")`. Book 1 Props 13–48 have empty `fig({})` stubs.
- Definitions use `#parallel([Greek], [English], n: N)` for numbering.
- `content-box-note` puts footnotes at the bottom of the enclosing `content-box`, not the page. Book subtitles use plain `#footnote`.
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
- `eps2svg.sh FILE.eps...` — EPS → SVG via `ps2pdf` and `pdftocairo`.

## Repo notes

- `tmp/` is gitignored scratch space. `*.pdf` is ignored, so build output never gets committed.
