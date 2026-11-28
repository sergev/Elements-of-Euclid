import Elements.Book10.Lemmas

namespace Elements.Book10

open Elements.Book5 Elements.Book5.Magnitude

variable {M : Type*} [Magnitude M]

/--
The step of 10.1: if `c` taken `p + j` times exceeds `x 0`, and from each `x n` is taken
`t`, not less than the remainder `x (n + 1)`, then `c` taken `p` times exceeds `x j`. From
`D E`, `c` taken `p + 1` times, is taken `c`, not more than half; from `x j`, less than
`D E`, is taken half or more: the remainder `x (j + 1)` is less than the remainder of
`D E`.
-/
theorem proposition_1_step {c : M} {x : ℕ → M}
    (hstep : ∀ n, ∃ t, x (n + 1) + t = x n ∧ x (n + 1) ≤ t) :
    ∀ (j : ℕ) (p k : ℕ+), (k : ℕ) = p + j → x 0 < k • c → x j < p • c := by
  intro j
  induction j with
  | zero => intro p k hk h; rwa [show k = p from PNat.eq hk] at h
  | succ j ih =>
    intro p k hk h
    have h' : x j < (p + 1) • c := ih (p + 1) k (by simp; omega) h
    obtain ⟨t, ht, hle⟩ := hstep j
    by_contra hge
    rw [not_lt] at hge
    -- `t` is not less than `x (j + 1)`, nor than `c` taken `p` times, nor than `c`
    have hc : c ≤ p • c := le_mult p c
    have : (p + 1) • c ≤ x j := by
      rw [mult_succ, ← ht]
      exact add_le_add hge (hc.trans (hge.trans hle))
    exact absurd h' (not_lt.mpr this)

/--
If from the greater `a` of two unequal magnitudes more than half is taken, and from the
remainder more than half, and so on continually, some remainder is less than the lesser
`c`. "Continually" is the sequence `x` of remainders, `x 0 = a`: from `x n` is taken `t`,
greater than the remainder `x (n + 1)`.
-/
theorem proposition_1 {a c : M} (_h : c < a) (x : ℕ → M) (hx : x 0 = a)
    (hstep : ∀ n, ∃ t, x (n + 1) + t = x n ∧ x (n + 1) < t) : ∃ n, x n < c := by
  -- `c`, multiplied, will sometime be greater than `a` [Def. 5.4]: let `D E` be such a
  -- multiple of `c`, divided into parts equal to `c`
  obtain ⟨m, hm⟩ := archimedes c a
  -- take from `a` more than half, and so on, until the divisions in `a` are as many as
  -- those in `D E`: the last remainder is less than `c`
  refine ⟨m.natPred, ?_⟩
  have := proposition_1_step (fun n => (hstep n).imp fun _ h => ⟨h.1, h.2.le⟩)
    m.natPred 1 m (by have := m.pos; simp [PNat.natPred]; omega) (hx ▸ hm)
  rwa [one_mult] at this

/-- 10.1, Euclid's closing remark: the same if halves are taken, the part taken equal to
the remainder. -/
theorem proposition_1' {a c : M} (_h : c < a) (x : ℕ → M) (hx : x 0 = a)
    (hstep : ∀ n, x (n + 1) + x (n + 1) = x n) : ∃ n, x n < c := by
  obtain ⟨m, hm⟩ := archimedes c a
  refine ⟨m.natPred, ?_⟩
  have := proposition_1_step (fun n => ⟨x (n + 1), hstep n, le_rfl⟩)
    m.natPred 1 m (by have := m.pos; simp [PNat.natPred]; omega) (hx ▸ hm)
  rwa [one_mult] at this

end Elements.Book10
