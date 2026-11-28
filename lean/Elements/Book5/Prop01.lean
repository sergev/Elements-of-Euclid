import Elements.Book5.Magnitude

namespace Elements.Book5

open Magnitude

variable {M : Type*} [Magnitude M]

/--
Euclid's case, two magnitudes: if `AB`, `CD` are equal multiples `m • e`, `m • f` of `E`,
`F`, then `AB` and `CD` together are the same multiple of `E` and `F` together.
-/
theorem proposition_1' (m : ℕ+) (e f : M) : m • e + m • f = m • (e + f) := by
  -- divide `AB` into `AG`, `GB`, … equal to `E`, and `CD` into `CH`, `HD`, … equal to `F`
  induction m using PNat.recOn with
  | one => rfl
  | succ m ih =>
    -- `GB` and `HD`, the last of them, are together equal to `E` and `F`
    rw [mult_succ, mult_succ, mult_succ, ← ih]
    exact add_add_add_comm _ _ _ _

/--
If any number of magnitudes `m • e 0`, …, `m • e n` are equal multiples of as many others
`e 0`, …, `e n`, then all of the first are the same multiple `m` of all of the second.
-/
theorem proposition_1 {n : ℕ} (m : ℕ+) (e : Fin (n + 1) → M) :
    sum (fun i => m • e i) = m • sum e := by
  induction n with
  | zero => rfl
  | succ n ih =>
    -- all but the last, and the last [Prop. 5.1, two magnitudes]
    simp only [sum]
    rw [ih, proposition_1']
