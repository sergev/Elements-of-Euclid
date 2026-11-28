import Elements.Book10.Prop004

namespace Elements.Book10

open Elements.Book5 Elements.Book5.Magnitude Number

variable {M : Type*} [Magnitude M]

/-- If `c` measures `a` according to the units in `m`, then as `c` is to `a`, so the unit
is to `m` [Def. 7.20]. -/
theorem proportion_unit (m : ℕ+) (c : M) : Proportion c (m • c) unit (m : Number) := by
  have := proportion_mult m c unit
  rwa [mult_unit] at this

/-- Commensurable magnitudes have to one another the ratio which a number has to a
number. -/
theorem proposition_5 {a b : M} (h : Commensurable a b) :
    ∃ m n : ℕ+, Proportion a b (m : Number) (n : Number) := by
  -- some magnitude `c` measures them, `a` according to the units in `m`, `b` according to
  -- the units in `n`
  obtain ⟨c, ⟨m, rfl⟩, ⟨n, rfl⟩⟩ := h
  -- as `c` is to `a`, so the unit to `m` [Def. 7.20]; inversely, as `a` to `c`, so `m` to
  -- the unit [Prop. 5.7 corr.]
  have h₁ := proposition_7_corollary (proportion_unit m c)
  -- as `c` is to `b`, so the unit to `n` [Def. 7.20]
  have h₂ := proportion_unit n c
  -- via equality, as `a` is to `b`, so `m` to `n` [Prop. 5.22]
  exact ⟨m, n, proposition_22' h₁ h₂⟩

end Elements.Book10
