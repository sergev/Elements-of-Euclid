import Elements.Book8.Prop16

namespace Elements.Book8

open Elements.Book7

/-- If a cube `c * c * c` does not measure a cube `d * d * d`, the side `c` will not
measure the side `d`; and if the side does not measure the side, the cube will not
measure the cube. -/
theorem proposition_17 {c d : ℕ} (hc : 0 < c) (hd : 0 < d) :
    (¬ c * c * c ∣ d * d * d → ¬ c ∣ d) ∧ (¬ c ∣ d → ¬ c * c * c ∣ d * d * d) :=
  -- if `c` measures `d`, the cube will measure the cube, and the other way round
  -- [Prop. 8.15]
  ⟨fun h hcd => h ((proposition_15 hc hd).2 hcd),
    fun h hcd => h ((proposition_15 hc hd).1 hcd)⟩

end Elements.Book8
