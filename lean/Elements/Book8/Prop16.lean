import Elements.Book8.Prop15

namespace Elements.Book8

open Elements.Book7

/-- If a square `c * c` does not measure a square `d * d`, the side `c` will not measure
the side `d`; and if the side does not measure the side, the square will not measure the
square. -/
theorem proposition_16 {c d : ℕ} (hc : 0 < c) (hd : 0 < d) :
    (¬ c * c ∣ d * d → ¬ c ∣ d) ∧ (¬ c ∣ d → ¬ c * c ∣ d * d) :=
  -- if `c` measures `d`, `c * c` will measure `d * d`, and the other way round
  -- [Prop. 8.14]
  ⟨fun h hcd => h ((proposition_14 hc hd).2 hcd),
    fun h hcd => h ((proposition_14 hc hd).1 hcd)⟩

end Elements.Book8
