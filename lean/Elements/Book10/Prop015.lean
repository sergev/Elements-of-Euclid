import Elements.Book10.Prop014

namespace Elements.Book10

open Elements.Book5

variable {M : Type*} [Magnitude M]

/-- If two commensurable magnitudes are added together, the whole is commensurable with
each of them; and if the whole is commensurable with one of them, `a`, the magnitudes are
commensurable. -/
theorem proposition_15 {a b : M} :
    (Commensurable a b → Commensurable (a + b) a ∧ Commensurable (a + b) b) ∧
      (Commensurable (a + b) a → Commensurable a b) := by
  constructor
  · -- some magnitude `d` measures `a` and `b`, and so the whole
    rintro ⟨d, ha, hb⟩
    exact ⟨⟨d, ha.add hb, ha⟩, ⟨d, ha.add hb, hb⟩⟩
  · -- some magnitude `d` measures the whole and `a`, and so the remainder `b`
    rintro ⟨d, hab, ha⟩
    exact ⟨d, ha, hab.sub ha⟩

end Elements.Book10
