import Elements.Book5.Prop16
import Elements.Book5.Prop19

namespace Elements.Book5

open Magnitude

variable {M : Type*} [Magnitude M]

/--
If four magnitudes are proportional, `AB : CD :: E : F`, with `AB` the greatest and `F`
the least, then the greatest and the least together are greater than the other two.
-/
theorem proposition_25 {a b c d : M} (h : Proportion a b c d)
    (ha : b < a ∧ c < a ∧ d < a) (hd : d < b ∧ d < c) : b + c < a + d := by
  -- let `AG` be made equal to `E`, and `CH` equal to `F`
  obtain ⟨g, hg⟩ := remainder c a ha.2.1
  obtain ⟨k, hk⟩ := remainder d b hd.1
  -- `AB : CD :: AG : CH`, so the remainder `GB` is to the remainder `HD` as `AB` to `CD`
  -- [Prop. 5.19]
  rw [← hg, ← hk] at h ha
  have h₁ := proposition_19 h
  -- `AB` is greater than `CD`, so `GB` is greater than `HD`
  -- Missed by Euclid: alternately `AB : GB :: CD : HD` [Prop. 5.16], then [Prop. 5.14]
  have hkg : k < g := (proposition_14 (proposition_16 h₁.symm)).1 ha.1
  -- `AG` and `F` are equal to `CH` and `E`; added to `GB` and to `HD`, the greater is
  -- `AB` and `F`
  calc b + c = (c + d) + k := by rw [← hk, add_right_comm, add_comm d c]
    _ < (c + d) + g := add_lt_add_of_le_of_lt le_rfl hkg
    _ = a + d := by rw [← hg, add_right_comm]
