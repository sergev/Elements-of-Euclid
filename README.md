# Euclid's Elements

The complete Elements of Euclid — all thirteen books of the most
famous mathematics book ever written, about 2300 years old.

## Download

Get the free PDF books from the [latest release](https://github.com/sergev/Elements-of-Euclid/releases/latest):

- [ElementsEnglish.pdf](https://github.com/sergev/Elements-of-Euclid/releases/latest/download/ElementsEnglish.pdf) — in English
- [ElementsGreekEnglish.pdf](https://github.com/sergev/Elements-of-Euclid/releases/latest/download/ElementsGreekEnglish.pdf) — the original Greek and the English side by side, with a small Greek–English dictionary
- [ElementsLean.pdf](https://github.com/sergev/Elements-of-Euclid/releases/latest/download/ElementsLean.pdf) — Books 1–5 in English, each proposition followed by its proof in the [Lean](https://lean-lang.org/) proof assistant

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
  The proofs of Books 2–4 were written for this edition in the same system,
  and those of Book 5 in plain Lean.
- Title picture: detail of Raphael's *School of Athens*.
- Book title pictures are drawn in the colorful style of Oliver Byrne's 1847 Euclid.

## Make the PDFs yourself

Install [Typst](https://typst.app/open-source/#download), then run `make` in this folder.

## Check the Lean proofs

The proofs of Books 1–5 are in [`lean/`](lean). Books 1–4 are written in System E,
a formal system for Euclid's style of geometry; Book 5, on proportion, is plain
Lean over a class of magnitudes. Every step is checked by the Lean kernel.

### Install Lean on Debian or Ubuntu

Lean is installed with its version manager, `elan`:

```sh
sudo apt install git curl
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
source ~/.elan/env
```

The Lean version is read from `lean/lean-toolchain`; `elan` downloads it on the
first build. The only Lean library used is Mathlib.

### Run the check

```sh
make cache          # download prebuilt Mathlib (a few GB, once)
make check          # check Books 1–5
make check BOOK=1   # check one book
```

The first `make check` builds the System E library and then the proofs; it takes
several minutes and about 6 GB of memory. A build that finishes without errors means
that every proposition is proved. To check one file while working on it:

```sh
cd lean
lake env lean --load-dynlib=.lake/build/lib/libelements_SaturateCore.so Elements/Book1/Prop47.lean
```

### SMT solvers (optional)

Each step of a proof is first closed by a built-in search that produces a proof
Lean can check. Only when that fails is the step handed to the SMT solvers Z3 and
CVC5, and the solvers' answer is then taken on trust. Books 1–5 need no solver,
so you can check them without installing any. To write new proofs, install the
solvers and `smt-portfolio`, which runs them in parallel:

```sh
sudo apt install z3 cvc5 pipx
pipx install git+https://github.com/yangky11/smt-portfolio
```

If your release has no `cvc5` package, take the Linux binary from the
[cvc5 releases](https://github.com/cvc5/cvc5/releases) and put it on your `PATH`
(for example in `~/.local/bin`). To see which theorems depend on a solver, run
`cd lean && lake env lean ../tools/SmtFree.lean`.
