# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

A Typst port of Richard Fitzpatrick's LaTeX edition of Euclid's Elements (Greek Heiberg text + English translation, side by side). The original LaTeX sources (`Elements.tex`, `BookNN/BookN.tex`, `BookNN/figNN{e,g}.eps`) are kept in the tree as the reference to port from. The Typst port currently covers only the introduction and Book 1.

## Build

```sh
typst compile ElementsTypst.typ          # produces ElementsTypst.pdf
typst watch ElementsTypst.typ            # rebuild on change
```

CeTZ (`@preview/cetz:0.4.2`) is fetched automatically by Typst. There are no tests; verify by compiling and inspecting the PDF. The LaTeX build (`latex Elements`) is legacy and not normally needed.

## Structure

- `ElementsTypst.typ` — root: page/footer/paragraph setup, then `#include`s `Book00/Introduction.typ` and `Book01/Book1.typ`.
- `functions.typ` — all shared layout helpers; every content file imports from it (`#import "../functions.typ": *`).
- `Book01/Book1.typ` — book title, running header, then `#include`s Definitions, Postulates, CommonNotions and `Prop01.typ`…`Prop48.typ` in order. A trailing `/* ... */` block holds not-yet-ported LaTeX.

### Proposition file pattern

Each `PropNN.typ` defines a figure function and a `content-box`:

```typst
#let figNN(letters) = fig({ import cetz.draw: * ... content(A, letters.at("A"), ...) })

#content-box[
  #parallel-proposition(NN, note: [...])   // optional footnote
  #parallel([Greek], [English])            // one call per paragraph pair
  #parallel-fig(figNN)                      // draws the figure twice: Greek and Latin labels
  ...
]
```

- `parallel-fig` calls the figure function twice with letter maps from `greek-map` (English letter → Greek letter, e.g. D→Δ, F→Ζ, G→Η, H→Θ). Labels must go through `letters.at("X")`, never be hard-coded. Add entries to `greek-map` if a figure needs letters beyond A–L.
- English math labels use `$A B$` (space-separated letters so Typst doesn't treat `AB` as a variable).
- `content-box-note` puts footnotes at the bottom of the enclosing `content-box`, not the page.
- `no-footer()` suppresses the page number on the current page (footer state is consumed once per page).
- `chapter(alt, body)` emits a heading whose outline entry differs from the displayed text.

## Port status / conventions

- Props 1–12 have CeTZ figures; Props 13–48 have empty `fig({})` stubs and empty English columns (Greek is filled in). Porting a proposition means: take the English text from the matching `\begin{Parallel}` block in `Book01/Book1.tex`, and reconstruct the figure from `Book01/figNNe.eps` geometry.
- Greek text is plain Unicode (copied from the LaTeX PDF), not italicized, with no hyphenation or kerning.
- CeTZ 0.4.2 handles polar coordinates poorly: build a point as `(r, 0)` and rotate with `cetz.vector.rotate-z(P, angle)`; use `cetz.vector.lerp/add/sub/dist` for constructions.

## Repo notes

- `tmp/` is gitignored scratch space.
