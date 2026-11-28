import SystemE.Theory.Sorts.Space

/-! Constructions in space. Each is true in ℝ³. -/

namespace Space

axiom line_from_points : ∀ (a b : Point), a ≠ b → ∃ L : Line, a.onLine L ∧ b.onLine L

/-- I.4: three points are on a plane. -/
axiom plane_from_points : ∀ (a b c : Point), ∃ π : Plane,
  a.onPlane π ∧ b.onPlane π ∧ c.onPlane π

/-- A line and a point are on a plane. -/
axiom plane_from_line : ∀ (L : Line) (a : Point), ∃ π : Plane, L.inPlane π ∧ a.onPlane π

/-- I.7: two planes with a common point have another. -/
axiom planes_meet : ∀ (a : Point) (π σ : Plane), a.onPlane π ∧ a.onPlane σ →
  ∃ b : Point, b ≠ a ∧ b.onPlane π ∧ b.onPlane σ

/-- I.8: a point off a plane. -/
axiom point_off_plane : ∀ (π : Plane), ∃ a : Point, ¬ a.onPlane π

/-- A point on the other side of a plane. -/
axiom point_opposite : ∀ (a : Point) (π : Plane), ¬ a.onPlane π →
  ∃ b : Point, ¬ b.onPlane π ∧ ¬ a.sameSide b π

/-- A segment joining opposite sides meets the plane. -/
axiom cross_plane : ∀ (a c : Point) (π : Plane),
  ¬ a.onPlane π ∧ ¬ c.onPlane π ∧ ¬ a.sameSide c π →
  ∃ b : Point, b.onPlane π ∧ between a b c

/-- A point of a plane is a point of System E's plane. -/
axiom pull_point : ∀ (a : Point) (π : Plane), a.onPlane π →
  ∃ a' : _root_.Point, π.over a' a

/-- A point of System E's plane is a point of each plane. -/
axiom push_point : ∀ (a' : _root_.Point) (π : Plane), ∃ a : Point, π.over a' a

axiom pull_line : ∀ (L : Line) (π : Plane), L.inPlane π →
  ∃ L' : _root_.Line, π.overLine L' L

axiom push_line : ∀ (L' : _root_.Line) (π : Plane), ∃ L : Line, π.overLine L' L

end Space
