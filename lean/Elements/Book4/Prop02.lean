import SystemE
import Elements.Book1.Prop11
import Elements.Book1.Prop13
import Elements.Book1.Prop23
import Elements.Book1.Prop32
import Elements.Book3.Prop16
import Elements.Book3.Prop32
import Elements.Book4.Lemmas

namespace Elements.Book4

/-- To inscribe in a circle `α`, with center `o`, a triangle equiangular with a given
triangle `DEF`. -/
theorem proposition_2 : ∀ (d e f o : Point) (DE EF FD : Line) (α : Circle),
  formTriangle d e f DE EF FD ∧ o.isCentre α →
  ∃ (a b c : Point) (AB BC CA : Line), formTriangle a b c AB BC CA ∧
  inscribedTriangle a b c α ∧ equiangularTriangles a b c d e f :=
by
  euclid_intros
  -- let GH be drawn touching the circle at A, at right angles to the radius OA
  -- [Props. 1.11, 3.16 corollary]
  euclid_apply (exists_point_on_circle α) as a
  euclid_apply (line_from_points o a) as OA
  euclid_apply (Elements.Book1.proposition_11_end a o OA) as h
  euclid_apply (line_from_points a h) as GH
  euclid_apply (extend_point GH h a) as g
  euclid_apply (intersection_circle_line_extending_points α OA o a) as a'
  euclid_apply (right_angle_on_lines o a h a' h OA GH)
  euclid_apply (Elements.Book3.proposition_16_corollary a a' o h GH α)
  -- HAC equal to DEF, and GAB equal to DFE [Prop. 1.23], toward the circle
  euclid_apply (Elements.Book1.proposition_23_side a h e d f o GH DE EF) as c'
  euclid_apply (Elements.Book1.proposition_23_side a g f d e o GH FD EF) as b'
  -- AC and AB cut the circle again, at C and B [Prop. 3.16]
  euclid_apply (line_from_points a c') as CA
  euclid_apply (line_from_points a b') as AB
  euclid_apply (Elements.Book3.proposition_16' a a' o h GH CA α)
  euclid_apply (Elements.Book3.proposition_16' a a' o h GH AB α)
  euclid_apply (other_intersection a CA α) as c
  euclid_apply (other_intersection a AB α) as b
  euclid_apply (equal_angles a c' c h h CA GH)
  euclid_apply (equal_angles a b' b g g AB GH)
  -- Missed by Euclid: B falls within the angle GAC, since GAB and HAC, being equal
  -- to DFE and DEF, are less than two right angles [Props. 1.13, 1.32].
  euclid_apply (extend_point EF e f) as x
  euclid_apply (Elements.Book1.proposition_32 d e f x DE EF FD)
  euclid_apply (Elements.Book1.proposition_13 c a h g CA GH)
  have : b.sameSide g CA := by
    by_contra
    by_cases (b.onLine CA)
    · euclid_apply (equal_angles a b c g g CA GH)
      euclid_finish
    · euclid_apply (sum_angles_onlyif a g b c GH AB)
      euclid_finish
  -- AH touches the circle, and AC is drawn across from A: HAC is equal to the angle ABC
  -- in the alternate segment [Prop. 3.32]; and so GAB is equal to ACB
  euclid_apply (points_on_both_sides a c h CA α) as (x₁, y₁)
  euclid_apply (Elements.Book3.proposition_32 a c g h o b y₁ CA GH α)
  euclid_apply (points_on_both_sides a b g AB α) as (x₂, y₂)
  euclid_apply (Elements.Book3.proposition_32 a b h g o c y₂ AB GH α)
  -- the remaining BAC is equal to EDF [Prop. 1.32]
  euclid_apply (line_from_points b c) as BC
  euclid_apply (extend_point BC b c) as z
  euclid_apply (Elements.Book1.proposition_32 a b c z AB BC CA)
  use a, b, c, AB, BC, CA
  euclid_finish

end Elements.Book4
