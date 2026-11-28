import Elements.Book5.Prop01
import Elements.Book5.Prop02
import Mathlib.Data.Nat.Find

namespace Elements.Book5

open Magnitude

variable {M : Type*} [Magnitude M]

/--
The first multiple of `D` greater than `K`, when `D` is not greater than `K`: it is
`(n + 1) • d`, and the one before it, `n • d`, is not greater than `K`.
-/
theorem proposition_8_lemma {d k : M} (h : d ≤ k) :
    ∃ n : ℕ+, k < (n + 1) • d ∧ n • d ≤ k := by
  classical
  -- some multiple of `D` is greater than `K` [Def. 5.4]
  have hex : ∃ j : ℕ, k < j.succPNat • d := by
    obtain ⟨p, hp⟩ := archimedes d k
    exact ⟨p.natPred, by rwa [PNat.succPNat_natPred]⟩
  -- take the double, the triple, … of `D`, until it is greater than `K`
  have hj : k < (Nat.find hex).succPNat • d := Nat.find_spec hex
  have hj0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at hj
    exact not_lt_of_ge h hj
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  refine ⟨i.succPNat, ?_, ?_⟩
  · have : i.succPNat + 1 = (Nat.find hex).succPNat := PNat.eq (by simp [hi])
    rw [this]
    exact hj
  · exact not_lt.mp (Nat.find_min hex (by omega : i < Nat.find hex))

/--
Of unequal magnitudes `AB` and `C`, the greater `AB` has a greater ratio to the same `D`
than the lesser `C`, and `D` has a greater ratio to the lesser `C` than to the greater
`AB`.
-/
theorem proposition_8 {a c : M} (h : c < a) (d : M) :
    GreaterRatio a d c d ∧ GreaterRatio d c d a := by
  -- let `BE` be made equal to `C`: `AB` is `AE` and `EB`
  obtain ⟨e, he⟩ := remainder c a h
  rw [add_comm] at he
  -- it is enough to find equal multiples `FH`, `K` of `AB`, `C`, and a multiple `N` of
  -- `D`, with `FH` exceeding `N` and `N` exceeding `K`
  suffices ∃ m n : ℕ+, n • d < m • a ∧ m • c < n • d by
    obtain ⟨m, n, h₁, h₂⟩ := this
    exact ⟨⟨m, n, h₁, not_lt_of_gt h₂⟩, ⟨n, m, h₂, not_lt_of_gt h₁⟩⟩
  -- `FH` and `K` are equal multiples of `AB` and `C` [Prop. 5.1]
  subst he
  simp only [← proposition_1']
  -- the lesser of `AE` and `EB`, multiplied, will exceed `D` [Def. 5.4]
  -- Missed by Euclid: `AE` equal to `EB` goes with the first case.
  rcases le_or_gt e c with hle | hlt
  · -- first, let `AE` be less than `EB`, and `FG`, a multiple of `AE`, greater than `D`;
    -- `GH` and `K` the same multiples of `EB` and `C`, so equal
    obtain ⟨m, hm⟩ := archimedes e d
    -- let `N` be the first multiple of `D` greater than `K`, and `M` the one before it
    obtain ⟨n, hN, hM⟩ := proposition_8_lemma (hm.trans_le (mult_le_mult m hle)).le
    refine ⟨m, n + 1, ?_, hN⟩
    -- `GH` is not less than `M`, and `FG` is greater than `D`: so `FH` is greater than
    -- `D` and `M` together, which is `N` [Prop. 5.2]
    rw [← proposition_2, one_mult, add_comm (m • e)]
    exact add_lt_add_of_le_of_lt hM hm
  · -- next, let `AE` be greater than `EB`, and `GH`, a multiple of `EB`, greater than `D`
    obtain ⟨m, hm⟩ := archimedes c d
    -- let `N` be the first multiple of `D` greater than `FG`, and `M` the one before it
    obtain ⟨n, hN, hM⟩ := proposition_8_lemma (hm.trans (mult_lt_mult m hlt)).le
    refine ⟨m, n + 1, ?_, ?_⟩
    · -- `FG` is not less than `M`, and `GH` is greater than `D`: so `FH` exceeds `N`
      rw [← proposition_2, one_mult]
      exact add_lt_add_of_le_of_lt hM hm
    · -- `K`, equal to `GH`, is less than `FG`, which does not exceed `N`
      exact (mult_lt_mult m hlt).trans hN
