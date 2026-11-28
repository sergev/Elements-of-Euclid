import Elements.Book5.Prop03
import Elements.Book5.Prop07
import Elements.Book5.Prop08

namespace Elements.Book5

open Magnitude

variable {M N : Type*} [Magnitude M] [Magnitude N]

/--
Missed by Euclid: a ratio is not both greater and less than another. If `A : B` is
greater than `C : D` by the multiples `m`, `n`, and `C : D` greater than `A : B` by `m'`,
`n'`, then `m' * n < m * n'` from `A`, `B`, and `m * n' < m' * n` from `C`, `D`.
-/
theorem proposition_10_lemma {a b : M} {c d : N} (h : GreaterRatio a b c d) :
    ¬ GreaterRatio c d a b := by
  rintro ⟨m', n', h₃, h₄⟩
  obtain ⟨m, n, h₁, h₂⟩ := h
  rw [not_lt] at h₂ h₄
  have hab : m' * n < m * n' := by
    apply lt_of_mult_lt_mult_left (a := b)
    calc (m' * n) • b = m' • (n • b) := (proposition_3 _ _ _).symm
      _ < m' • (m • a) := mult_lt_mult m' h₁
      _ = m • (m' • a) := by rw [proposition_3, proposition_3, mul_comm]
      _ ≤ m • (n' • b) := mult_le_mult m h₄
      _ = (m * n') • b := proposition_3 _ _ _
  have hcd : m * n' < m' * n := by
    apply lt_of_mult_lt_mult_left (a := d)
    calc (m * n') • d = m • (n' • d) := (proposition_3 _ _ _).symm
      _ < m • (m' • c) := mult_lt_mult m h₃
      _ = m' • (m • c) := by rw [proposition_3, proposition_3, mul_comm]
      _ ≤ m' • (n • d) := mult_le_mult m' h₂
      _ = (m' * n) • d := proposition_3 _ _ _
  exact lt_asymm hab hcd

/--
Of magnitudes `A`, `B` having a ratio to the same `C`, that which has the greater ratio
is greater.
-/
theorem proposition_10 {a b c : M} (h : GreaterRatio a c b c) : b < a := by
  rcases lt_trichotomy b a with h' | rfl | h'
  · exact h'
  · -- `A` is not equal to `B`: they would have the same ratio to `C` [Prop. 5.7]
    exact absurd h (proposition_7 c rfl).1.not_greaterRatio
  · -- nor less: `A` would have a lesser ratio to `C` than `B` has [Prop. 5.8]
    exact absurd (proposition_8 h' c).1 (proposition_10_lemma h)

/-- That magnitude `B` to which the same `C` has the greater ratio is the lesser. -/
theorem proposition_10' {a b c : M} (h : GreaterRatio c b c a) : b < a := by
  rcases lt_trichotomy b a with h' | rfl | h'
  · exact h'
  · -- `B` is not equal to `A`: `C` would have the same ratio to each [Prop. 5.7]
    exact absurd h (proposition_7 c rfl).2.not_greaterRatio
  · -- nor greater: `C` would have a lesser ratio to `B` than to `A` [Prop. 5.8]
    exact absurd (proposition_8 h' c).2 (proposition_10_lemma h)
