import Elements.Book5.Prop02

namespace Elements.Book5

open Magnitude

variable {M N : Type*} [Magnitude M] [Magnitude N]

/--
If two magnitudes `AB`, `CD` are equal multiples `m • e`, `m • f` of two magnitudes `E`,
`F`, and `AG`, `CH`, taken away, are equal multiples `n • e`, `n • f` of them, then the
remainders `GB`, `HD` are either equal to `E`, `F`, or equal multiples of them.
-/
theorem proposition_6 {m n : ℕ+} {a b e : M} {c d f : N}
    (h₁ : a + b = m • e) (h₂ : c + d = m • f) (h₃ : a = n • e) (h₄ : c = n • f) :
    (b = e ∧ d = f) ∨ ∃ k : ℕ+, b = k • e ∧ d = k • f := by
  -- Missed by Euclid: `GB` is equal to `E`, or a multiple `k • e` of it
  have hnm : n < m := by
    exact lt_of_mult_lt_mult_left (h₃ ▸ h₁ ▸ lt_add a b)
  set k := m - n
  have hm : n + k = m := PNat.add_sub_of_lt hnm
  have hb : b = k • e := by
    rw [← hm, ← proposition_2, h₃] at h₁
    exact add_left_cancel h₁
  -- if `GB` is `k • e`, then `HD` is `k • f`:
  have hd : d = k • f := by
    -- let `CK` be made equal to `k • f`; `AB`, `KH` are equal multiples of `E`, `F`
    -- [Prop. 5.2]
    have hAB : a + b = (n + k) • e := by rw [h₃, hb, proposition_2]
    have hKH : c + k • f = (n + k) • f := by rw [h₄, proposition_2]
    -- `AB`, `CD` are equal multiples of `E`, `F`: so `KH` is equal to `CD`
    have : n + k = m := mult_inj_left (hAB.symm.trans h₁)
    rw [this, ← h₂] at hKH
    -- take `CH` away from both: `KC` is equal to `HD`
    exact (add_left_cancel hKH).symm
  -- `GB` equal to `E`, first, or a multiple of it
  by_cases hk : k = 1
  · left
    rw [hb, hd, hk, one_mult, one_mult]
    exact ⟨rfl, rfl⟩
  · exact Or.inr ⟨k, hb, hd⟩
