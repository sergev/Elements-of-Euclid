import Elements.Book5.Prop14
import Elements.Book5.Prop17

namespace Elements.Book5

open Magnitude

variable {M N : Type*} [Magnitude M] [Magnitude N]

/--
If separated magnitudes are proportional, `AE : EB :: CF : FD`, then they are also
proportional composed, `AB : BE :: CD : DF`. `fourth` is a fourth proportional to `AB`,
`BE`, `CD`, which Euclid assumes.
-/
theorem proposition_18 {a b : M} {c d : N} (h : Proportion a b c d)
    (fourth : ∃ x : N, Proportion (a + b) b (c + d) x) :
    Proportion (a + b) b (c + d) d := by
  -- if not, then as `AB` to `BE`, so `CD` to some `DG`, less or greater than `DF`
  -- Missed by Euclid: a fourth proportional exists.
  obtain ⟨x, hx⟩ := fourth
  -- Missed by Euclid: `DG` is less than `CD` [Def. 5.5]
  have hxc : x < c + d := (hx.gt 1 1).mp (lt_add' a b)
  obtain ⟨g, hg⟩ := remainder x (c + d) hxc
  rw [← hg, add_comm x g] at hx
  -- `AE : EB :: CG : GD` [Prop. 5.17], and `AE : EB :: CF : FD`, so `CG : GD :: CF : FD`
  -- [Prop. 5.11]
  have h₁ := proposition_11 (proposition_17 hx).symm h
  rcases lt_trichotomy x d with hlt | rfl | hgt
  · -- `DG` less than `DF`: the first `CG` is greater than the third `CF`, so the second
    -- `GD` is greater than the fourth `FD` [Prop. 5.14]; but it is also less
    have : c < g := lt_of_not_ge fun h' =>
      absurd hg (ne_of_lt (by rw [add_comm c d]; exact add_lt_add_of_lt_of_le hlt h'))
    exact absurd ((proposition_14 h₁).1 this) (not_lt_of_gt hlt)
  · -- so `CD` is to `DF` itself
    rwa [← hg, add_comm x g]
  · -- similarly, `DG` greater than `DF`
    have : g < c := lt_of_not_ge fun h' =>
      absurd hg (ne_of_gt (by rw [add_comm c d]; exact add_lt_add_of_lt_of_le hgt h'))
    exact absurd ((proposition_14 h₁).2.2 this) (not_lt_of_gt hgt)
