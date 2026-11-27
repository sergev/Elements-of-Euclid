# Euclid's Elements

The complete Elements of Euclid — all thirteen books of the most
famous mathematics book ever written, about 2300 years old.

## Download

Get the free PDF books from the [latest release](https://github.com/sergev/Elements-of-Euclid/releases/latest):

- [ElementsEnglish.pdf](https://github.com/sergev/Elements-of-Euclid/releases/latest/download/ElementsEnglish.pdf) — in English
- [ElementsGreekEnglish.pdf](https://github.com/sergev/Elements-of-Euclid/releases/latest/download/ElementsGreekEnglish.pdf) — the original Greek and the English side by side, with a small Greek–English dictionary
- [ElementsLean.pdf](https://github.com/sergev/Elements-of-Euclid/releases/latest/download/ElementsLean.pdf) — Book 1 in English, each proposition followed by its proof in the [Lean](https://lean-lang.org/) proof assistant

## What's inside

- Books 1–6: geometry of the plane — lines, triangles, circles, proportions
- Books 7–10: numbers and incommensurable magnitudes
- Books 11–13: solid geometry, up to the five regular solids

The propositions come with their diagrams.

## Credits

- Greek text: J.L. Heiberg (1883–1885).
- English translation: Richard Fitzpatrick, University of Texas at Austin,
  from his [original edition](https://github.com/rfitzp/Elements).
- Lean proofs of Book 1: [LeanEuclid](https://github.com/loganrjmurphy/LeanEuclid)
  by L. Murphy, K. Yang et al. (MIT license), written in the formal system E
  of Avigad, Dean and Mumma. The interface to the SMT solvers comes from
  [lean-smt](https://github.com/ufmg-smite/lean-smt) (Apache 2.0).
- Title picture: detail of Raphael's *School of Athens*.
- Book title pictures are drawn in the colorful style of Oliver Byrne's 1847 Euclid.

## Make the PDFs yourself

Install [Typst](https://typst.app/open-source/#download), then run `make` in this folder.
To check the Lean proofs, install [Lean](https://lean-lang.org/), Z3, CVC5
and `smt-portfolio`, then run `make check`.
