import Elements.Book5.Prop16
import Elements.Book5.Prop17

namespace Elements.Book5

variable {M : Type*} [Magnitude M]

/--
If as the whole `AB` is to the whole `CD`, so `AE`, taken away, is to `CF`, taken away,
then the remainder `EB` is to the remainder `FD` as the whole to the whole.
-/
theorem proposition_19 {a b c d : M} (h : Proportion (a + b) (c + d) a c) :
    Proportion b d (a + b) (c + d) := by
  -- alternately, `BA : AE :: DC : CF` [Prop. 5.16]
  have h₁ := proposition_16 h
  -- separated, `BE : EA :: DF : FC` [Prop. 5.17]
  rw [add_comm a b, add_comm c d] at h₁
  have h₂ := proposition_17 h₁
  -- alternately, `BE : DF :: EA : FC` [Prop. 5.16], and `AE : CF :: AB : CD`
  -- [Prop. 5.11]
  exact proposition_11 (proposition_16 h₂) h.symm

/--
If composed magnitudes are proportional, `AB : BE :: CD : DF`, then they are also
proportional converted, `BA : AE :: DC : CF`.
-/
theorem proposition_19_corollary {a b c d : M} (h : Proportion (a + b) b (c + d) d) :
    Proportion (a + b) a (c + d) c := by
  -- Missed by Euclid: alternately, `AB : CD :: BE : DF` [Prop. 5.16]
  have h₁ := proposition_16 h
  -- Missed by Euclid: as whole to whole, so `BE`, taken away, to `DF`, taken away; so the
  -- remainder `AE` to the remainder `CF` [Prop. 5.19]
  rw [add_comm a b, add_comm c d] at h₁
  have h₂ := proposition_19 h₁
  rw [add_comm b a, add_comm d c] at h₂
  -- Missed by Euclid: so `AB : CD :: AE : CF`, and alternately `BA : AE :: DC : CF`
  -- [Prop. 5.16]
  exact proposition_16 h₂.symm
