import Elements.Book10.Prop009

namespace Elements.Book10

open Elements.Book5

variable {M N : Type*} [Magnitude M] [Magnitude N]

/--
If four magnitudes are proportional, and the first is commensurable with the second, the
third is commensurable with the fourth; and if the first is incommensurable with the
second, so the third with the fourth. Through 10.6 and 10.7, the magnitudes divided into
equal parts (`Divisible`).
-/
theorem proposition_11 {a b : M} {c d : N} (h : Proportion a b c d) (hM : Divisible M)
    (hN : Divisible N) :
    (Commensurable a b → Commensurable c d) ∧
      (¬ Commensurable a b → ¬ Commensurable c d) := by
  constructor
  · -- `a` has to `b` the ratio which a number has to a number [Prop. 10.5], and so `c` to
    -- `d` [Prop. 5.11]: they are commensurable [Prop. 10.6]
    intro hab
    obtain ⟨m, n, h'⟩ := proposition_5 hab
    exact proposition_6 (Elements.Book5.proposition_11 h.symm h') (hN c m)
  · -- `a` does not have to `b` the ratio which a number has to a number [Prop. 10.7], nor
    -- does `c` to `d`: they are incommensurable [Prop. 10.8]
    intro hab
    apply proposition_8
    rintro ⟨m, n, h'⟩
    exact proposition_7 hab (hM a) ⟨m, n, Elements.Book5.proposition_11 h h'⟩

end Elements.Book10
