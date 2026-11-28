import Elements.Book10.Definitions2

/-
The six irrational differences (10.73–10.78) and Defs. III, the six apotomes (before
10.85): the terms of `Definitions2.lean`, the lesser `y` (the line attached) taken from
the greater `x` (the whole), leaving `l`, `l + y = x`.
-/

namespace Elements.Book10

open Elements.Book5

/-- 10.73: an apotome. -/
def Apotome (ρ l : Length) : Prop := ∃ x y, BinomialTerms ρ x y ∧ l + y = x

/-- 10.74: a first apotome of a medial. -/
def FirstApotomeOfMedial (ρ l : Length) : Prop :=
  ∃ x y, FirstBimedialTerms ρ x y ∧ l + y = x

/-- 10.75: a second apotome of a medial. -/
def SecondApotomeOfMedial (ρ l : Length) : Prop :=
  ∃ x y, SecondBimedialTerms ρ x y ∧ l + y = x

/-- 10.76: a minor line. -/
def Minor (ρ l : Length) : Prop := ∃ x y, MajorTerms ρ x y ∧ l + y = x

/-- 10.77: that which with a rational area makes a medial whole. -/
def MedialWholeWithRational (ρ l : Length) : Prop :=
  ∃ x y, RationalMedialTerms ρ x y ∧ l + y = x

/-- 10.78: that which with a medial area makes a medial whole. -/
def MedialWholeWithMedial (ρ l : Length) : Prop :=
  ∃ x y, TwoMedialTerms ρ x y ∧ l + y = x

/-- Def. 10.III.1: a first apotome. -/
def FirstApotome (ρ r l : Length) : Prop := ∃ x y, FirstTerms ρ r x y ∧ l + y = x

/-- Def. 10.III.2: a second apotome. -/
def SecondApotome (ρ r l : Length) : Prop := ∃ x y, SecondTerms ρ r x y ∧ l + y = x

/-- Def. 10.III.3: a third apotome. -/
def ThirdApotome (ρ r l : Length) : Prop := ∃ x y, ThirdTerms ρ r x y ∧ l + y = x

/-- Def. 10.III.4: a fourth apotome. -/
def FourthApotome (ρ r l : Length) : Prop := ∃ x y, FourthTerms ρ r x y ∧ l + y = x

/-- Def. 10.III.5: a fifth apotome. -/
def FifthApotome (ρ r l : Length) : Prop := ∃ x y, FifthTerms ρ r x y ∧ l + y = x

/-- Def. 10.III.6: a sixth apotome. -/
def SixthApotome (ρ r l : Length) : Prop := ∃ x y, SixthTerms ρ r x y ∧ l + y = x

end Elements.Book10
