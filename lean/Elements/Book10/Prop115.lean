import Elements.Book10.Prop114

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- The lines of 10.115: from `a`, each the side of the square equal to the rectangle
contained by the rational `ρ` and the line before [Prop. 2.14]. -/
noncomputable def medialSeq (ρ a : Length) : ℕ → Length
  | 0 => a
  | n + 1 => Classical.choose (Area.side (rect ρ (medialSeq ρ a n)))

theorem medialSeq_succ (ρ a : Length) (n : ℕ) :
    sq (medialSeq ρ a (n + 1)) = rect ρ (medialSeq ρ a n) :=
  Classical.choose_spec (Area.side (rect ρ (medialSeq ρ a n)))

/--
From a medial line `a` arise infinitely many irrational lines, none the same as any before
it: the line `x (n + 1)` whose square is the rectangle contained by `ρ` and `x n`, from
`x 0 = a`. Each is irrational, and "not the same as any before" is read as incommensurable
in square with each before it: so not equal to it, nor commensurable with it in length.
Euclid's reason, that the square on none of the lines before, applied to a rational line,
makes the line before as breadth, is the step `x i`, `x n` incommensurable in length.
-/
theorem proposition_115 {a : Length} (ha : Medial ρ a) :
    ∃ x : ℕ → Length, x 0 = a ∧ (∀ n, sq (x (n + 1)) = rect ρ (x n)) ∧
      ∀ n, ¬ Rational ρ (x n) ∧ ∀ i < n, ¬ CommensurableInSquare (x n) (x i) := by
  refine ⟨medialSeq ρ a, rfl, medialSeq_succ ρ a, fun n => ?_⟩
  induction n with
  | zero =>
    -- `a` is medial, so irrational [Prop. 10.21]
    obtain ⟨y, z, hy, hz, hyz, h⟩ := ha
    exact ⟨(proposition_21 hy hz hyz).2 a h, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ n ih =>
    obtain ⟨hirr, hinc⟩ := ih
    have hs := medialSeq_succ ρ a n
    -- the rectangle contained by the rational `ρ` and the irrational `x n` is irrational
    -- [Prop. 10.20], and so `x (n + 1)` [Def. 10.4]
    have h₁ : ¬ Rational ρ (medialSeq ρ a (n + 1)) := fun h =>
      hirr (proposition_20 (Rational.self ρ) (hs ▸ h.sq_rational) rfl).1
    refine ⟨h₁, fun i hi => ?_⟩
    rw [CommensurableInSquare, hs]
    rcases i with _ | i
    · -- not with `a`: else the rectangle on `ρ` would be medial [Prop. 10.23 corr.], and
      -- applied to `ρ` it would make `x n` rational as breadth [Prop. 10.22]
      intro h
      exact hirr (proposition_22' (proposition_23_corollary ha h) (Rational.self ρ) rfl).1
    · -- not with `x (i + 1)`: else `x n` would be commensurable in length with `x i`
      -- [Props. 6.1, 10.11], and so in square [Prop. 10.9 corr.]
      rw [medialSeq_succ, rect_commensurable_iff]
      exact fun h => hinc i (by omega) (proposition_9_corollary h)

end Elements.Book10
