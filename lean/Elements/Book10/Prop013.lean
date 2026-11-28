import Elements.Book10.Prop012

namespace Elements.Book10

open Elements.Book5

variable {M : Type*} [Magnitude M]

/-- If two magnitudes are commensurable, and one of them is incommensurable with some
magnitude, the other is incommensurable with it. Through 10.12. -/
theorem proposition_13 (hM : Divisible M) {a b c : M} (hab : Commensurable a b)
    (hac : ¬ Commensurable a c) : ¬ Commensurable b c :=
  -- if `b` is commensurable with `c`, `a`, commensurable with `b`, is commensurable with
  -- `c` [Prop. 10.12]
  fun hbc => hac (proposition_12 hM hab hbc.symm)

/--
10.13, lemma: for two unequal lines, to find the line by whose square the square on the
greater exceeds that on the lesser: in a semicircle on the greater `a`, the lesser `b`
inserted [Prop. 4.1], the angle in the semicircle is right [Prop. 3.31], and the square
on `a` is the squares on `b` and on the third side [Prop. 1.47]. And likewise the line
whose square is the squares on two lines [Prop. 1.47]. Constructions of the model
(`Length.exceeds`, `Length.hypotenuse`).
-/
theorem proposition_13_lemma {a b : Length} (h : b < a) :
    (∃ c, sq b + sq c = sq a) ∧ ∃ c, sq a + sq b = sq c :=
  ⟨Length.exceeds h, Length.hypotenuse a b⟩

end Elements.Book10
