import SystemE.Space
import Elements.Book6

/-
Book 11's definitions, over the points, lines and planes of space (`SystemE/Space.lean`).
-/

namespace Elements.Book11

open Elements.Book5 Elements.Book6

/-- Def. 11.3: the straight line `ab` is at right angles to the plane `π` at `b`: it
makes right angles with every straight line joined to it in the plane. -/
@[simp] abbrev RightToPlane (a b : Space.Point) (π : Space.Plane) : Prop :=
  b.onPlane π ∧ ¬ a.onPlane π ∧
    ∀ c : Space.Point, c.onPlane π → c ≠ b → Space.angle a b c = ∟

/-- Def. 11.4: the plane `π` is at right angles to `σ`: the straight lines drawn in `π` at
right angles to the common section are at right angles to `σ`. -/
@[simp] abbrev PlaneRightToPlane (π σ : Space.Plane) : Prop :=
  π ≠ σ ∧ ∀ a b c : Space.Point, a.onPlane π → b.onPlane π → b.onPlane σ →
    c.onPlane π → c.onPlane σ → b ≠ c → ¬ a.onPlane σ → Space.angle a b c = ∟ →
    RightToPlane a b σ

/-- Def. 11.8: parallel planes do not meet. -/
@[simp] abbrev ParallelPlanes (π σ : Space.Plane) : Prop :=
  ∀ p : Space.Point, p.onPlane π → ¬ p.onPlane σ

/-- Parallel straight lines in space (Def. 1.23): in one plane, and not meeting. -/
def Parallel (L M : Space.Line) : Prop :=
  ∃ π : Space.Plane, L.inPlane π ∧ M.inPlane π ∧
    ∀ p : Space.Point, p.onLine L → ¬ p.onLine M

/-- Volumes are a kind of magnitude, as lengths and areas are (Book 6's `Kind`). -/
noncomputable instance : Kind Volume where
  of x h := ⟨x, h⟩
  of_inj := Subtype.mk_eq_mk
  of_add _ _ := Subtype.ext (Positive.coe_add _ _)
  of_lt := Iff.rfl

end Elements.Book11
