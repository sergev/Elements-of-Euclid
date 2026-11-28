import SystemE.Theory.Relations

/-!
Space, for Book 11 on: points, lines and planes, with their relations and measures.
System E's `Point`, `Line` are one plane; every plane of space carries a copy of it
(`Plane.over`).
-/

namespace Space

/-- Points of space. -/
axiom Point : Type

/-- Lines of space. -/
axiom Line : Type

/-- Planes. -/
axiom Plane : Type

opaque Point.onLine : Point → Line → Prop
opaque Point.onPlane : Point → Plane → Prop
opaque Line.inPlane : Line → Plane → Prop

/-- `between a b c`: `b` is between `a` and `c`. -/
opaque between : Point → Point → Point → Prop

/-- `p`, `q` are on the same side of the plane `π`, neither on it. -/
opaque Point.sameSide : Point → Point → Plane → Prop

/-- The length of the straight line `ab`. -/
opaque dist : Point → Point → ℝ

/-- The angle `abc`, at `b`. -/
opaque angle : Point → Point → Point → ℝ

/-- The area of the triangle `abc`. -/
opaque area : Point → Point → Point → ℝ

/-- The volume of the tetrahedron (pyramid) `abcd`. -/
opaque volume : Point → Point → Point → Point → ℝ

/-- `π.over a' a`: the point `a'` of System E's plane is the point `a` of the plane
`π`. -/
opaque Plane.over : Plane → _root_.Point → Point → Prop

/-- `π.overLine L' L`: System E's line `L'` is the line `L` of the plane `π`. -/
opaque Plane.overLine : Plane → _root_.Line → Line → Prop

end Space
