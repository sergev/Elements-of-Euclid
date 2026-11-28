import Elements.Book10.Prop001

namespace Elements.Book10

open Elements.Book5 Elements.Book5.Magnitude

variable {M : Type*} [Magnitude M]

/--
`b`, taken from `a` as often as it can be, leaves `c`, less than itself:
`a = k • b + c`. The step of the process of 10.2, as Book 7's `remainder` is for numbers.
-/
def Leaves (a b c : M) : Prop := ∃ k : ℕ+, a = k • b + c ∧ c < b

/--
The process of 10.2, which never ends: `r 0` and `r 1` are the magnitudes, the lesser
`r 1` is taken from the greater as often as it can be, leaving `r 2`, then `r 2` from
`r 1`, and so on continually, the remainder never measuring the magnitude before it.
-/
def NeverMeasures (r : ℕ → M) : Prop := ∀ n, Leaves (r n) (r (n + 1)) (r (n + 2))

/-- A lesser magnitude that does not measure a greater leaves a remainder. -/
theorem exists_leaves {a b : M} (h : b < a) (hm : ¬ Measures b a) :
    ∃ c, Leaves a b c := by
  obtain ⟨k, hk, hk'⟩ := Elements.Book5.proposition_8_lemma h.le
  rcases hk'.lt_or_eq with hlt | heq
  · obtain ⟨c, hc⟩ := remainder _ _ hlt
    refine ⟨c, k, hc.symm, ?_⟩
    rw [mult_succ, ← hc] at hk
    exact lt_of_add_lt_add_left hk
  · exact absurd ⟨k, heq.symm⟩ hm

/-- A common measure of `r 0` and `r 1` measures every remainder of the process. -/
theorem NeverMeasures.measures {r : ℕ → M} (h : NeverMeasures r) {e : M}
    (h₀ : Measures e (r 0)) (h₁ : Measures e (r 1)) : ∀ n, Measures e (r n) := by
  have : ∀ n, Measures e (r n) ∧ Measures e (r (n + 1)) := by
    intro n
    induction n with
    | zero => exact ⟨h₀, h₁⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      -- `e` measures `r (n + 1)`, and so what `r (n + 1)` measures in `r n`; and the
      -- whole `r n`: so the remainder `r (n + 2)`
      obtain ⟨k, hk, -⟩ := h n
      exact (hk ▸ ih.1).sub (ih.2.mult k)
  exact fun n => (this n).1

/--
If, the lesser of two unequal magnitudes being taken in turn from the greater continually,
the remainder never measures the magnitude before it, the magnitudes are incommensurable.
-/
theorem proposition_2 {r : ℕ → M} (h : NeverMeasures r) :
    ¬ Commensurable (r 0) (r 1) := by
  -- if they are commensurable, some magnitude `e` measures them
  rintro ⟨e, h₀, h₁⟩
  -- `e` measures every remainder
  have he := h.measures h₀ h₁
  -- and some remainder is less than `e` [Prop. 10.1]: from `r (2 n)` is taken more than
  -- half, what `r (2 n + 1)` measures in it, leaving `r (2 n + 2)`
  have hlt : e < r 0 := by
    obtain ⟨k, hk, hlt⟩ := h 0
    exact lt_of_le_of_lt h₁.le (hk ▸ lt_of_le_of_lt (le_mult k _) (lt_add _ _))
  obtain ⟨n, hn⟩ := proposition_1 hlt (fun n => r (2 * n)) rfl fun n => by
    obtain ⟨k, hk, hlt⟩ := h (2 * n)
    refine ⟨k • r (2 * n + 1), ?_, ?_⟩
    · rw [hk, add_comm]; rfl
    · exact lt_of_lt_of_le hlt (le_mult k _)
  -- the greater measuring the lesser, which is impossible
  exact absurd (he (2 * n)).le (not_le.mpr hn)

end Elements.Book10
