import Elements.Book11.Definitions

/-
Lemmas for Book 11: lengths in space as magnitudes.
-/

namespace Elements.Book11

open Elements.Book5

theorem dist_pos {a b : Space.Point} (h : a ≠ b) : 0 < Space.dist a b :=
  lt_of_le_of_ne (Space.dist_nonneg a b) fun h' => h (Space.dist_zero a b h'.symm)

/-- The length of the straight line `ab` in space, `a ≠ b`. -/
noncomputable def len (a b : Space.Point) (h : a ≠ b) : Length := ⟨_, dist_pos h⟩

end Elements.Book11
