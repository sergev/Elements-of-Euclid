import Elements.Book10.Definitions

/-
The six irrational sums (10.36–10.41), by the conditions on their terms, and Defs. II,
the six binomials (before 10.48). The six differences (10.73–10.78) and Defs. III have the
same conditions on their terms (`Definitions3.lean`), the lesser taken from the greater.
-/

namespace Elements.Book10

open Elements.Book5

/-! The terms `x` and `y` of the irrational sums and differences, the greater `x`. -/

/-- 10.36, 10.73: rational lines, commensurable in square only. -/
def BinomialTerms (ρ x y : Length) : Prop :=
  Rational ρ x ∧ Rational ρ y ∧ InSquareOnly x y ∧ y < x

/-- 10.37, 10.74: medial lines, commensurable in square only, containing a rational
area. -/
def FirstBimedialTerms (ρ x y : Length) : Prop :=
  Medial ρ x ∧ Medial ρ y ∧ InSquareOnly x y ∧ RationalArea ρ (rect x y) ∧ y < x

/-- 10.38, 10.75: medial lines, commensurable in square only, containing a medial
area. -/
def SecondBimedialTerms (ρ x y : Length) : Prop :=
  Medial ρ x ∧ Medial ρ y ∧ InSquareOnly x y ∧ MedialArea ρ (rect x y) ∧ y < x

/-- 10.39, 10.76: lines incommensurable in square, the sum of the squares on them
rational, the rectangle contained by them medial. -/
def MajorTerms (ρ x y : Length) : Prop :=
  ¬ CommensurableInSquare x y ∧ RationalArea ρ (sq x + sq y) ∧ MedialArea ρ (rect x y) ∧
    y < x

/-- 10.40, 10.77: lines incommensurable in square, the sum of the squares on them
medial, the rectangle contained by them rational. -/
def RationalMedialTerms (ρ x y : Length) : Prop :=
  ¬ CommensurableInSquare x y ∧ MedialArea ρ (sq x + sq y) ∧ RationalArea ρ (rect x y) ∧
    y < x

/-- 10.41, 10.78: lines incommensurable in square, the sum of the squares on them medial,
the rectangle contained by them medial, and incommensurable with the sum of the
squares. -/
def TwoMedialTerms (ρ x y : Length) : Prop :=
  ¬ CommensurableInSquare x y ∧ MedialArea ρ (sq x + sq y) ∧ MedialArea ρ (rect x y) ∧
    ¬ Commensurable (sq x + sq y) (rect x y) ∧ y < x

/-! The six irrational sums. -/

/-- 10.36: a binomial, the sum of two rational lines commensurable in square only. -/
def Binomial (ρ l : Length) : Prop := ∃ x y, BinomialTerms ρ x y ∧ l = x + y

/-- 10.37: a first bimedial. -/
def FirstBimedial (ρ l : Length) : Prop := ∃ x y, FirstBimedialTerms ρ x y ∧ l = x + y

/-- 10.38: a second bimedial. -/
def SecondBimedial (ρ l : Length) : Prop := ∃ x y, SecondBimedialTerms ρ x y ∧ l = x + y

/-- 10.39: a major line. -/
def Major (ρ l : Length) : Prop := ∃ x y, MajorTerms ρ x y ∧ l = x + y

/-- 10.40: the square root of a rational plus a medial area. -/
def SideRationalMedial (ρ l : Length) : Prop :=
  ∃ x y, RationalMedialTerms ρ x y ∧ l = x + y

/-- 10.41: the square root of two medial areas. -/
def SideTwoMedials (ρ l : Length) : Prop := ∃ x y, TwoMedialTerms ρ x y ∧ l = x + y

/-! Defs. II: the six binomials, relative to a rational line `r` laid out. -/

/-- The square on `x` exceeds the square on `y` by the square on a line commensurable in
length with `x`. -/
def ExceedsComm (x y : Length) : Prop := ∃ z, sq y + sq z = sq x ∧ Commensurable z x

/-- The square on `x` exceeds the square on `y` by the square on a line incommensurable
in length with `x`. -/
def ExceedsIncomm (x y : Length) : Prop := ∃ z, sq y + sq z = sq x ∧ ¬ Commensurable z x

/-- Defs. 10.II.1, 10.III.1: binomial terms, the square on the greater exceeding that on
the lesser by the square on a line commensurable with the greater, and the greater
commensurable in length with `r`. -/
def FirstTerms (ρ r x y : Length) : Prop :=
  BinomialTerms ρ x y ∧ ExceedsComm x y ∧ Commensurable x r

/-- Defs. 10.II.2, 10.III.2: as the first, but the lesser commensurable with `r`. -/
def SecondTerms (ρ r x y : Length) : Prop :=
  BinomialTerms ρ x y ∧ ExceedsComm x y ∧ Commensurable y r

/-- Defs. 10.II.3, 10.III.3: as the first, but neither commensurable with `r`. -/
def ThirdTerms (ρ r x y : Length) : Prop :=
  BinomialTerms ρ x y ∧ ExceedsComm x y ∧ ¬ Commensurable x r ∧ ¬ Commensurable y r

/-- Defs. 10.II.4, 10.III.4: binomial terms, the square on the greater exceeding that on
the lesser by the square on a line incommensurable with the greater, and the greater
commensurable in length with `r`. -/
def FourthTerms (ρ r x y : Length) : Prop :=
  BinomialTerms ρ x y ∧ ExceedsIncomm x y ∧ Commensurable x r

/-- Defs. 10.II.5, 10.III.5: as the fourth, but the lesser commensurable with `r`. -/
def FifthTerms (ρ r x y : Length) : Prop :=
  BinomialTerms ρ x y ∧ ExceedsIncomm x y ∧ Commensurable y r

/-- Defs. 10.II.6, 10.III.6: as the fourth, but neither commensurable with `r`. -/
def SixthTerms (ρ r x y : Length) : Prop :=
  BinomialTerms ρ x y ∧ ExceedsIncomm x y ∧ ¬ Commensurable x r ∧ ¬ Commensurable y r

/-- Def. 10.II.1: a first binomial. -/
def FirstBinomial (ρ r l : Length) : Prop := ∃ x y, FirstTerms ρ r x y ∧ l = x + y

/-- Def. 10.II.2: a second binomial. -/
def SecondBinomial (ρ r l : Length) : Prop := ∃ x y, SecondTerms ρ r x y ∧ l = x + y

/-- Def. 10.II.3: a third binomial. -/
def ThirdBinomial (ρ r l : Length) : Prop := ∃ x y, ThirdTerms ρ r x y ∧ l = x + y

/-- Def. 10.II.4: a fourth binomial. -/
def FourthBinomial (ρ r l : Length) : Prop := ∃ x y, FourthTerms ρ r x y ∧ l = x + y

/-- Def. 10.II.5: a fifth binomial. -/
def FifthBinomial (ρ r l : Length) : Prop := ∃ x y, FifthTerms ρ r x y ∧ l = x + y

/-- Def. 10.II.6: a sixth binomial. -/
def SixthBinomial (ρ r l : Length) : Prop := ∃ x y, SixthTerms ρ r x y ∧ l = x + y

end Elements.Book10
