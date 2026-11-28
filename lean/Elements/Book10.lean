import Elements.Book10.Definitions
import Elements.Book10.Definitions2
import Elements.Book10.Definitions3
import Elements.Book10.Lemmas
import Elements.Book10.Prop001
import Elements.Book10.Prop002
import Elements.Book10.Prop003
import Elements.Book10.Prop004
import Elements.Book10.Prop005
import Elements.Book10.Prop006
import Elements.Book10.Prop007
import Elements.Book10.Prop008
import Elements.Book10.Prop009
import Elements.Book10.Prop010
import Elements.Book10.Prop011
import Elements.Book10.Prop012
import Elements.Book10.Prop013
import Elements.Book10.Prop014
import Elements.Book10.Prop015
import Elements.Book10.Prop016
import Elements.Book10.Prop017
import Elements.Book10.Prop018
import Elements.Book10.Prop019
import Elements.Book10.Prop020
import Elements.Book10.Prop021
import Elements.Book10.Prop022
import Elements.Book10.Prop023
import Elements.Book10.Prop024
import Elements.Book10.Prop025
import Elements.Book10.Prop026
import Elements.Book10.Prop027
import Elements.Book10.Prop028
import Elements.Book10.Prop029
import Elements.Book10.Prop030
import Elements.Book10.Prop031
import Elements.Book10.Prop032
import Elements.Book10.Prop033
import Elements.Book10.Prop034
import Elements.Book10.Prop035
import Elements.Book10.Prop036
import Elements.Book10.Prop037
import Elements.Book10.Prop038
import Elements.Book10.Prop039
import Elements.Book10.Prop040
import Elements.Book10.Prop041
import Elements.Book10.Prop042
import Elements.Book10.Prop043
import Elements.Book10.Prop044
import Elements.Book10.Prop045
import Elements.Book10.Prop046
import Elements.Book10.Prop047
import Elements.Book10.Prop048
import Elements.Book10.Prop049
import Elements.Book10.Prop050
import Elements.Book10.Prop051
import Elements.Book10.Prop052
import Elements.Book10.Prop053
import Elements.Book10.Prop054
import Elements.Book10.Prop055
import Elements.Book10.Prop056
import Elements.Book10.Prop057
import Elements.Book10.Prop058
import Elements.Book10.Prop059
import Elements.Book10.Prop060
import Elements.Book10.Prop061
import Elements.Book10.Prop062
import Elements.Book10.Prop063
import Elements.Book10.Prop064
import Elements.Book10.Prop065
import Elements.Book10.Prop066
import Elements.Book10.Prop067
import Elements.Book10.Prop068
import Elements.Book10.Prop069
import Elements.Book10.Prop070
import Elements.Book10.Prop071
import Elements.Book10.Prop072

/-
Book 10: incommensurable magnitudes.

Plain Lean over Book 5's magnitudes (`Elements/Book5/Magnitude.lean`): no System E and no
saturation. Ratios are Book 5's `Proportion` (Def. 5.5), and Book 5's propositions are
cited as Lean terms, as Book 6 does. There is no division of magnitudes, and Mathlib's
`Irrational`, `ℚ` and `Real.sqrt` appear in no statement and no step Euclid takes.

Two layers:
- 10.1–10.8, 10.11–10.13, 10.15 and 10.16 are about any magnitudes, `[Magnitude M]`.
- From 10.9 on, the magnitudes are lines and areas, `Length` and `Area`
  (`Elements/Book5/Plane.lean`), positive reals. The square on a line, `sq a`, and the
  rectangle contained by two lines, `rect a b`, are areas, products of lengths, as in
  Book 2. A `Length` is a magnitude, not a segment of System E's plane, so Book 2's and
  Book 6's propositions, which are about points, cannot be cited: the facts of theirs that
  Book 10 uses are lemmas of the model in `Lemmas.lean`, each naming its proposition (6.1
  `rect_proportion`, 6.20 `squaredRatio_sq`, 6.22 `proportion_sq`, 2.1 `rect_add`, 2.4
  `sq_add`, 2.7 `sq_add_sq_of_sub`).

Definitions (`Definitions.lean`):
- `Measures c a`: `a = n • c` for some `n : ℕ+`. Def. 10.1, `Commensurable a b`: some
  magnitude measures both; incommensurable is its negation.
- Def. 10.2, `CommensurableInSquare a b`: the squares are commensurable;
  `InSquareOnly a b` adds incommensurable in length.
- Numbers. "The ratio which a number has to a number" (10.5–10.9) is Book 5's proportion
  between magnitudes and numbers, so numbers are a kind of magnitude: `Number`, which is
  `ℕ+` under another name (so that `n • a` is Book 5's multiple, not Mathlib's product).
  Def. 5.5 for four numbers agrees with Def. 7.20 (`number_proportion_iff`, marked missed:
  Euclid passes between them without comment), so Books 7–9 can be cited.
- Def. 10.3: an assigned line `ρ` is a parameter. `Rational ρ x`: `x` commensurable with
  `ρ` in length, or in square only. Def. 10.4, `RationalArea ρ A`: `A` commensurable with
  `sq ρ`. Irrational lines and areas are the negations. Prop. 10.21's medial area,
  `MedialArea ρ A`, is the rectangle contained by rational lines commensurable in square
  only, and a medial line `Medial ρ x` one whose square is a medial area.

The twelve irrational sums and differences (`Definitions2.lean`, `Definitions3.lean`) are
pairs of terms `x > y` with one of six conditions (`BinomialTerms`, `FirstBimedialTerms`,
`SecondBimedialTerms`, `MajorTerms`, `RationalMedialTerms`, `TwoMedialTerms`): the sum
`l = x + y` is a binomial, first or second bimedial, major, side of a rational plus a
medial area, side of two medial areas (10.36–10.41); the difference `l + y = x` an
apotome, first or second apotome of a medial, minor, that which with a rational (a
medial) area makes a medial whole (10.73–10.78). Defs. II and III, the six binomials and
apotomes, are one condition on the terms (`FirstTerms`, …, `SixthTerms`) relative to a
rational line `r` laid out, with plus or minus. So a proof about the terms serves both
halves.

Constructions, facts of the model in `Lemmas.lean`, each with its proposition: a part of a
line (6.9, `Length.part`), a fourth proportional (6.12, `Length.fourth'`), a mean
proportional (6.13, `Length.mean`), a square equal to an area (2.14, `Area.side`), a
rectangle applied to a line (1.44, `Area.apply`), falling short or exceeding by a square
(6.28 `Area.apply_short`, 6.29 `Area.apply_excess`), and the line by whose square the
square on the greater exceeds that on the lesser (3.31 with 1.47, `Length.exceeds`).

Files have three digits, `Prop001.lean`; the theorems are `proposition_1`, …
-/
