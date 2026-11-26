# Euclid's Elements

## Typst

This is a simple rewrite of Euclid's Elements from Richard
Fitzpatrick's LaTeX repo. Each book and proposition is split into
its own file, with helper functions in `/functions.typ` to
provide for consistent styles throughout. The layout is not
exactly the same as Fitzpatrick's -- the different typesetting
engine is different, Typst does not currently hyphenate Greek,
and the typeface is not (yet?) the same. Also, this conversion
maintains parallel paragraphs, which makes the text line up better
in some places, but worse in others.

All thirteen books and the Greek-English lexicon are included.
The Typst sources were generated from the LaTeX files with the
scripts in `tools/` and then proofread: the Greek is converted from
the LaTeX transliteration to Unicode (`tools/greek.py`), and the
figures and the frontispieces of Books 10-13 are SVGs converted
from the original EPS files, except Book 1 figures 1-12, which are
redrawn in CeTZ.

Functions are provided to aid in parallel layout, including

- `no-footer()` to suppress page number on the current page
- `fig(body)` sets up CeTZ environment for `body`
- `#parallel([left column text], [right column text])`,
- `#parallel-heading([left column text], [right column text], heading depth)`
- `#parallel-fig(fig-function)` (pass in fig-function(letters)
  to set labels with `#content(point, letters.at("letter"))`)
- `content-box(body)`
- `content-box-note(text)` provides footnotes that render at the bottom of 
  `content-box` instead of at the bottom of the page
- `#parallel-image("/BookNN/figNN", height)` places the Greek and English
  versions of an SVG figure side by side
- `#parallel-subheading([Greek], [English])` for lemmas and corollaries

Depends on [Typst](https://typst.app) for typesetting 
and [CeTZ](https://cetz-package.github.io/) (automatically imported) for figures.

Use [Typst CLI](https://typst.app/open-source/#download)
or upload everything to the GUI for compilation.

The document can be compiled by issuing the command

`make` (or `typst compile ElementsTypst.typ`)

in the base directory (containing `ElementsTypst.typ`).

## Some Notes

Greek text is in Unicode (precomposed polytonic), converted
from the transliterated Greek of the LaTeX source. Hyphenation
has been removed.

Greek text does not implement kerning indicated in the LaTeX source.

Greek text is not italicized. This may be changed later.

Paragraph spacing is wider than the original.

CeTZ does not currently (0.4.2) handle alternate coordinates well. 
To use a radius-angle coordinate, do `#let A = (radius, 0)` then 
`A = cetz.vector.rotate-z(A, angle)`.

# From rfitzp/Elements

The original repository contains the LaTeX files to compile
a Greek/English version of Euclid's Elements. The Greek text
is the standard Heiberg edition. The modern English translation 
was authored by Prof. Richard Fitzpatrick (Department of Physics, 
University of Texas at Austin).

The LaTeX build and the EPS figures have been removed from this
repository; the LaTeX text of each book is kept as a reference.
