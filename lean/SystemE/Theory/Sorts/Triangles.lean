import SystemE.Theory.Sorts.Segments

/--
Triangles are called "Areas" in [Avigad et al., 2009]
-/
inductive Triangle
| ofPoints (a b c : Point)

namespace Triangle

opaque area : Triangle → ℝ

notation:max "△" a ":" b ":" c:66 => ofPoints a b c

/-- Area of the parallelogram `formParallelogram a b c d`, cut by the diagonal `ad`. -/
notation:max "▱" a ":" b ":" c ":" d:66 => (Triangle.area (△ a:c:d) + Triangle.area (△ a:b:d))

noncomputable instance : Coe Triangle Real := ⟨area⟩

instance : LT Triangle := ⟨fun a b => area a < area b⟩

end Triangle
