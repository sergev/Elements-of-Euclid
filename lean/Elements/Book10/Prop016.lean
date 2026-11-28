import Elements.Book10.Prop015

namespace Elements.Book10

open Elements.Book5

variable {M : Type*} [Magnitude M]

/-- If two incommensurable magnitudes are added together, the whole is incommensurable
with each of them; and if the whole is incommensurable with one of them, `a`, the
magnitudes are incommensurable. -/
theorem proposition_16 {a b : M} :
    (¬ Commensurable a b → ¬ Commensurable (a + b) a ∧ ¬ Commensurable (a + b) b) ∧
      (¬ Commensurable (a + b) a → ¬ Commensurable a b) := by
  constructor
  · intro h
    constructor
    · -- if some magnitude `d` measures the whole and `a`, it measures the remainder
      -- `b`: `a` and `b` are commensurable, which is impossible
      rintro ⟨d, hab, ha⟩
      exact h ⟨d, ha, hab.sub ha⟩
    · -- so, similarly, for the whole and `b`
      rintro ⟨d, hab, hb⟩
      exact h ⟨d, (add_comm a b ▸ hab).sub hb, hb⟩
  · -- if some magnitude `d` measures `a` and `b`, it measures the whole: the whole and
    -- `a` are commensurable, which is impossible
    rintro h ⟨d, ha, hb⟩
    exact h ⟨d, ha.add hb, ha⟩

/--
10.16, lemma: if a parallelogram falling short by a square figure is applied to a line,
the applied parallelogram is the rectangle contained by the pieces of the line. Here the
line is cut into `x` and `y`, the applied figure is the rectangle on `x` of height `d`,
and the defect, the rectangle on `y` of height `d`, is a square: so `d` is `y`, and the
applied figure is the rectangle contained by `x` and `y`.
-/
theorem proposition_16_lemma {x y d : Length} (h : rect y d = sq y) :
    rect x d = rect x y := by
  -- since the defect is a square, `d` is equal to `y`
  have : d = y := rect_inj h
  rw [this]

end Elements.Book10
