import SystemE.Book4

/-!
Book 6's geometric definitions, over System E's relations and Book 4's figures. Those
with ratios are in `Elements/Book6/Definitions.lean`, since ratios are Book 5's.
-/

/-- A quadrilateral `abcd`, as a figure with an area. -/
inductive Quadrilateral
| ofPoints (a b c d : Point)

notation:max "□" a ":" b ":" c ":" d:66 => Quadrilateral.ofPoints a b c d

/-- A pentagon `abcde`, as a figure with an area. -/
inductive Pentagon
| ofPoints (a b c d e : Point)

notation:max "⬠" a ":" b ":" c ":" d ":" e:66 => Pentagon.ofPoints a b c d e

/-- The area of the quadrilateral `abcd`: the triangles `abc`, `acd` of the diagonal
from `a`. -/
@[simp]
abbrev Quadrilateral.area : Quadrilateral → ℝ
  | ofPoints a b c d => Triangle.area △a:b:c + Triangle.area △a:c:d

/-- The area of the pentagon `abcde`: the triangles `abc`, `acd`, `ade` of the diagonals
from `a`. -/
@[simp]
abbrev Pentagon.area : Pentagon → ℝ
  | ofPoints a b c d e =>
    Triangle.area △a:b:c + Triangle.area △a:c:d + Triangle.area △a:d:e

/-- Quadrilaterals `abcd` and `efgh` are equiangular, the angles at `a`, `b`, `c`, `d`
equal to those at `e`, `f`, `g`, `h`. -/
@[simp]
abbrev equiangularQuadrilaterals (a b c d e f g h : Point) : Prop :=
  ∠ d:a:b = ∠ h:e:f ∧ ∠ a:b:c = ∠ e:f:g ∧ ∠ b:c:d = ∠ f:g:h ∧ ∠ c:d:a = ∠ g:h:e

/-- Pentagons `abcde` and `fghkl` are equiangular, angle by angle in order. -/
@[simp]
abbrev equiangularPentagons (a b c d e f g h k l : Point) : Prop :=
  ∠ e:a:b = ∠ l:f:g ∧ ∠ a:b:c = ∠ f:g:h ∧ ∠ b:c:d = ∠ g:h:k ∧ ∠ c:d:e = ∠ h:k:l ∧
  ∠ d:e:a = ∠ k:l:f

/-- Def. 6.3, as Prop. 6.1 uses it: figures on bases on the line `BC` with vertices `a`,
`d` are under the same height when `a` and `d` are on a line `AD` parallel to `BC`. -/
@[simp]
abbrev sameHeight (a d : Point) (AD BC : Line) : Prop :=
  a.onLine AD ∧ d.onLine AD ∧ ¬ AD.intersectsLine BC
