import SystemE
import SystemE.Theory.Sorts.Space
import SystemE.Theory.Inferences.Space
import SystemE.Theory.Constructions.Space

/-! Space (Book 11 on): its objects and lemmas join saturation's. -/

namespace Space

theorem point_ne_symm : ∀ (a b : Point), a ≠ b → b ≠ a := fun _ _ h => h.symm

theorem line_ne_symm : ∀ (L M : Line), L ≠ M → M ≠ L := fun _ _ h => h.symm

theorem plane_ne_symm : ∀ (π σ : Plane), π ≠ σ → σ ≠ π := fun _ _ h => h.symm

theorem point_ne_of_on_line : ∀ (a b : Point) (L : Line),
    a.onLine L ∧ ¬ b.onLine L → a ≠ b := fun _ _ _ ⟨h, hn⟩ e => hn (e ▸ h)

theorem line_ne_of_on_line : ∀ (a : Point) (L M : Line),
    a.onLine L ∧ ¬ a.onLine M → L ≠ M := fun _ _ _ ⟨h, hn⟩ e => hn (e ▸ h)

theorem point_ne_of_on_plane : ∀ (a b : Point) (π : Plane),
    a.onPlane π ∧ ¬ b.onPlane π → a ≠ b := fun _ _ _ ⟨h, hn⟩ e => hn (e ▸ h)

theorem plane_ne_of_on_plane : ∀ (a : Point) (π σ : Plane),
    a.onPlane π ∧ ¬ a.onPlane σ → π ≠ σ := fun _ _ _ ⟨h, hn⟩ e => hn (e ▸ h)

theorem line_ne_of_in_plane : ∀ (L M : Line) (π : Plane),
    L.inPlane π ∧ ¬ M.inPlane π → L ≠ M := fun _ _ _ ⟨h, hn⟩ e => hn (e ▸ h)

theorem point_ne_of_same_side : ∀ (a b c : Point) (π : Plane),
    a.sameSide c π ∧ ¬ b.sameSide c π → a ≠ b := fun _ _ _ _ ⟨h, hn⟩ e => hn (e ▸ h)

/-- The sides of a triangle meet only at its vertices. -/
theorem ne_of_lines_ne : ∀ (a c b : Point) (L M : Line),
    a.onLine L ∧ b.onLine L ∧ b.onLine M ∧ c.onLine M ∧ a ≠ b ∧ L ≠ M → a ≠ c := by
  intro a c b L M ⟨haL, hbL, hbM, hcM, hab, hLM⟩ hac
  subst hac
  exact hLM (line_unique a b L M ⟨hab, haL, hbL, hcM, hbM⟩)

/-- A vertex of a triangle is not on the opposite side's line. -/
theorem not_on_line_of_triangle : ∀ (c a b : Point) (L M N : Line),
    a.onLine L ∧ b.onLine L ∧ c.onLine M ∧ b.onLine M ∧ c.onLine N ∧ a.onLine N ∧
    a ≠ b ∧ L ≠ M ∧ L ≠ N → ¬ c.onLine L := by
  intro c a b L M N ⟨haL, hbL, hcM, hbM, hcN, haN, hab, hLM, hLN⟩ hcL
  have hac : a ≠ c := ne_of_lines_ne a c b L M ⟨haL, hbL, hbM, hcM, hab, hLM⟩
  exact hLN (line_unique a c L N ⟨hac, haL, hcL, haN, hcN⟩)

end Space

namespace SystemE.Saturate

initialize configRef.modify fun c => { c with
  objectSorts := c.objectSorts ++ #[``Space.Point, ``Space.Line, ``Space.Plane]
  lemmas := c.lemmas ++ #[``Space.point_ne_symm, ``Space.line_ne_symm,
    ``Space.plane_ne_symm, ``Space.point_ne_of_on_line, ``Space.line_ne_of_on_line,
    ``Space.point_ne_of_on_plane, ``Space.plane_ne_of_on_plane,
    ``Space.line_ne_of_in_plane, ``Space.point_ne_of_same_side]
  backwardLemmas := c.backwardLemmas ++
    #[``Space.ne_of_lines_ne, ``Space.not_on_line_of_triangle] }

end SystemE.Saturate
