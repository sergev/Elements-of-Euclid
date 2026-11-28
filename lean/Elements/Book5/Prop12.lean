import Elements.Book5.Prop01

namespace Elements.Book5

open Magnitude

variable {M : Type*} [Magnitude M]

/--
If any number of magnitudes are proportional, `A : B :: C : D :: E : F :: …`, then as one
of the leading is to one of the following, so are all the leading to all the following.
The leading are `a 0`, …, `a n`, and the following `b 0`, …, `b n`.
-/
theorem proposition_12 {n : ℕ} {a b : Fin (n + 1) → M}
    (h : ∀ i, Proportion (a 0) (b 0) (a i) (b i)) :
    Proportion (a 0) (b 0) (sum a) (sum b) := by
  -- let equal multiples `G`, `H`, `K`, … of `A`, `C`, `E`, … be taken, and `L`, `M`,
  -- `N`, … of `B`, `D`, `F`, …; all of `G`, `H`, `K`, … are the same multiple of all of
  -- `A`, `C`, `E`, … as `G` of `A`, and likewise for `L`, `M`, `N`, … [Prop. 5.1]
  apply Proportion.of_imp <;> intro m k h₁ <;> rw [← proposition_1, ← proposition_1]
  -- if `G` exceeds `L`, `H` exceeds `M`, `K` exceeds `N`, … [Def. 5.5]: all exceed all
  · exact sum_lt_sum fun i => ((h i).gt m k).mp h₁
  -- the same if equal
  · exact sum_eq_sum fun i => ((h i).eq m k).mp h₁
  -- and if less
  · exact sum_lt_sum fun i => ((h i).lt m k).mp h₁
