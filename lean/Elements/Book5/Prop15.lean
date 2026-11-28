import Elements.Book5.Prop12

namespace Elements.Book5

open Magnitude

variable {M : Type*} [Magnitude M]

/-- Parts `C`, `F` have the same ratio as equal multiples `AB`, `DE` of them. -/
theorem proposition_15 (c f : M) (m : ℕ+) : Proportion c f (m • c) (m • f) := by
  -- divide `AB` into `AG`, `GH`, `HB`, … equal to `C`, and `DE` into `DK`, `KL`, `LE`, …
  -- equal to `F`, as many
  rw [← PNat.succPNat_natPred m, ← sum_const, ← sum_const]
  -- `AG : DK :: GH : KL :: HB : LE …`, being equal [Prop. 5.7]; so `AG : DK :: AB : DE`
  -- [Prop. 5.12]
  exact proposition_12 (a := fun _ => c) (b := fun _ => f) fun _ => Proportion.refl c f
