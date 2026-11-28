import Elements.Book8

/-
The notions of Book 9, over Book 7's numbers. Book 9 has no definitions of its own: these
are Book 7's definitions of odd and even (Defs. 7.6–7.10), which Book 7 left to Book 9,
and the least number measured by any multitude (7.36, for any multitude).
-/

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/-- Def. 7.6: an even number is one divided in half, into two equal numbers `h`. The half
may be the unit (`2 = 1 + 1`). -/
def EvenNumber (a : ℕ) : Prop := ∃ h, 0 < h ∧ a = h + h

/--
Def. 7.7: an odd number is one not divided in half. The unit counts as odd: it is not
divided in half, and Euclid's sums and products of odd numbers (9.22, 9.23, 9.29) and his
"even or odd" (9.30) take it so. Def. 7.7's second reading, "differs from an even number
by a unit", is `odd_iff`; for the unit, the even number is nothing.
-/
def OddNumber (a : ℕ) : Prop := 0 < a ∧ ¬ EvenNumber a

/-- Def. 7.8: an even-times-even number is measured by an even number according to an
even number, `a = e * f`. -/
def EvenTimesEven (a : ℕ) : Prop := ∃ e f, EvenNumber e ∧ EvenNumber f ∧ a = e * f

/--
Def. 7.9: an even-times-odd number is measured by an even number according to an odd
number. The odd number is a number (Def. 7.2), greater than the unit: else every even
number would be even-times-odd, measured by itself according to the unit, and 9.32 would
fail (`4 = 4 * 1`).
-/
def EvenTimesOdd (a : ℕ) : Prop :=
  ∃ e f, EvenNumber e ∧ OddNumber f ∧ 1 < f ∧ a = e * f

/-- Def. 7.10: an odd-times-odd number is measured by an odd number according to an odd
number, both numbers (greater than the unit), as in Def. 7.9. -/
def OddTimesOdd (a : ℕ) : Prop :=
  ∃ e f, OddNumber e ∧ OddNumber f ∧ 1 < e ∧ 1 < f ∧ a = e * f

/-- `c` is the least number that `a 0`, …, `a n` measure: Book 7's `LeastMeasured` (7.34)
and `LeastMeasured₃` (7.36), for any multitude (9.14, 9.20). -/
def LeastMeasuredSeq {n : ℕ} (c : ℕ) (a : Fin (n + 1) → ℕ) : Prop :=
  0 < c ∧ (∀ i, a i ∣ c) ∧ ∀ d, 0 < d → (∀ i, a i ∣ d) → c ≤ d

end Elements.Book9
