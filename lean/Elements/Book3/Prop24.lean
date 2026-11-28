import SystemE
import Elements.Book1.Prop10
import Elements.Book3.Prop20
import Elements.Book3.Prop23

namespace Elements.Book3

/-
Prop. 3.24. Euclid applies the segment `AEB` to `CFD`; System E superposes triangles. Here
the triangle `ABO` on the chord, `O` the center, is applied to `CD`, and the circle with
center at the image of `O` through `C` and `D` has a segment on `CD` similar to `CFD`; it
is `CFD`'s circle [Prop. 3.23]. The segments, on equal chords of equal circles (Def. 3.1),
coincide; that is what "equal" means here.
-/

/-- Applied with its center `O'` on the side of `Y` of `CD`, the circle is `β`. -/
theorem proposition_24_apply :
  ∀ (a b c d x y o o' p : Point) (AB CD : Line) (α β : Circle),
  similarSegments α a b AB x β c d CD y ∧ |(a─b)| = |(c─d)| ∧
  o.isCentre α ∧ p.isCentre β ∧
  |(o─a)| = |(o'─c)| ∧ |(o─b)| = |(o'─d)| ∧ ∠ a:o:b = ∠ c:o':d ∧ ¬(o'.onLine CD) ∧
  ((o.sameSide x AB ∧ o'.sameSide y CD) ∨
   (o.opposingSides x AB ∧ o'.opposingSides y CD)) →
  |(o─a)| = |(p─c)| :=
by
  euclid_intros
  -- the circle γ with center O' through C passes through D
  euclid_apply (point_on_circle_onlyif o a b α)
  euclid_apply (circle_from_points o' c) as γ
  euclid_apply (point_on_circle_if o' c d γ)
  euclid_apply (Elements.Book1.proposition_10 c d CD) as m
  euclid_apply (line_from_points m o') as MO
  rcases ‹_ ∨ _› with ⟨_, _⟩ | ⟨_, _⟩
  · -- a point Y' of γ beyond O' from M: the angle in its segment is half of CO'D,
    -- as AXB is half of AOB [Prop. 3.20]
    euclid_apply (intersection_circle_line_extending_points γ MO o' m) as y'
    euclid_apply (proposition_20 x a b o AB α)
    euclid_apply (proposition_20 y' c d o' CD γ)
    -- γ and β have similar segments on CD: they are one circle [Prop. 3.23]
    euclid_apply (proposition_23 c d y' y o' p CD γ β)
    euclid_apply (centre_unique o' p β)
    euclid_finish
  · -- likewise with a point Y' of γ beyond M from O' [Prop. 3.20, in the other position]
    euclid_apply (circle_points_between c d m γ)
    euclid_apply (intersection_circle_line_extending_points γ MO m o') as y'
    euclid_apply (proposition_20' x a b o AB α)
    euclid_apply (proposition_20' y' c d o' CD γ)
    euclid_apply (proposition_23 c d y' y o' p CD γ β)
    euclid_apply (centre_unique o' p β)
    euclid_finish

/-- Similar segments `AEB`, `CFD` on equal straight lines `AB`, `CD` are equal. -/
theorem proposition_24 : ∀ (a b c d x y o p : Point) (AB CD : Line) (α β : Circle),
  similarSegments α a b AB x β c d CD y ∧ |(a─b)| = |(c─d)| ∧
  o.isCentre α ∧ p.isCentre β →
  |(o─a)| = |(p─c)| :=
by
  euclid_intros
  by_cases (o.onLine AB)
  · -- Missed by Euclid: AB is a diameter, the angles in the segments are right, and
    -- CD is a diameter too
    euclid_apply (proposition_20'' x a b o AB α)
    by_cases (p.onLine CD)
    · euclid_apply (circle_line_intersections o a b AB α)
      euclid_apply (circle_line_intersections p c d CD β)
      euclid_apply (point_on_circle_onlyif o a b α)
      euclid_apply (point_on_circle_onlyif p c d β)
      euclid_apply (between_if a o b)
      euclid_apply (between_if c p d)
      euclid_finish
    · exfalso
      by_cases (p.sameSide y CD)
      · euclid_apply (proposition_20 y c d p CD β)
        euclid_apply (flat_angle_if c p d)
        euclid_finish
      · euclid_apply (proposition_20' y c d p CD β)
        euclid_apply (flat_angle_if c p d)
        euclid_finish
  · -- apply AB to CD, the center to the side of the segment CFD as it is to AEB
    euclid_apply (line_from_points b o) as BO
    euclid_apply (line_from_points o a) as OA
    by_cases (o.sameSide x AB)
    · euclid_apply (superposition a b o c d y AB BO OA CD) as (b', o', BO', CO')
      euclid_apply (point_on_circle_onlyif o a b α)
      euclid_apply (eq_of_same_ray b' d c CD)
      euclid_apply (proposition_24_apply a b c d x y o o' p AB CD α β)
      euclid_finish
    · euclid_apply (exists_point_opposite CD y) as y'
      euclid_apply (superposition a b o c d y' AB BO OA CD) as (b', o', BO', CO')
      euclid_apply (point_on_circle_onlyif o a b α)
      euclid_apply (eq_of_same_ray b' d c CD)
      euclid_apply (proposition_24_apply a b c d x y o o' p AB CD α β)
      euclid_finish

end Elements.Book3
