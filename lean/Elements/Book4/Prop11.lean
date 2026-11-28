import SystemE
import Elements.Book1.Prop09
import Elements.Book1.Prop32
import Elements.Book3.Prop21
import Elements.Book3.Prop22
import Elements.Book3.Prop26
import Elements.Book3.Prop27
import Elements.Book3.Prop28
import Elements.Book3.Prop29
import Elements.Book4.Lemmas
import Elements.Book4.Prop02
import Elements.Book4.Prop10

namespace Elements.Book4

/--
Prop. 3.27 for circumferences greater than semicircles, the centers across `BC`, `EF`
from `A`, `D`: the angles at points `X`, `Y` on the remaining circumferences are equal
[Prop. 3.27], and with `BAC`, `EDF` make two right angles [Prop. 3.22].
-/
theorem proposition_11_greater : ∀ (a b c d e f g h : Point) (BC EF : Line)
    (α β : Circle),
  g.isCentre α ∧ h.isCentre β ∧ a.onCircle α ∧ b.onCircle α ∧ c.onCircle α ∧
  d.onCircle β ∧ e.onCircle β ∧ f.onCircle β ∧ |(g─b)| = |(h─e)| ∧
  distinctPointsOnLine b c BC ∧ distinctPointsOnLine e f EF ∧
  g.opposingSides a BC ∧ h.opposingSides d EF ∧ α.arc b c a = β.arc e f d →
  ∠ b:a:c = ∠ e:d:f :=
by
  euclid_intros
  euclid_apply (points_on_both_sides b c a BC α) as (x, x')
  euclid_apply (points_on_both_sides e f d EF β) as (y, y')
  -- the remaining circumferences are equal
  euclid_apply (Elements.Book3.arc_whole b c a x BC α)
  euclid_apply (Elements.Book3.arc_whole e f d y EF β)
  euclid_apply (Elements.Book3.circumference_eq g b h e α β)
  euclid_apply (Elements.Book3.proposition_27 x b c y e f g h BC EF α β)
  -- ABXC and DEYF are quadrilaterals in circles [Prop. 3.22]
  euclid_apply (line_from_points a x) as AX
  euclid_apply (line_from_points d y) as DY
  euclid_apply (intersection_lines_opposing a x BC AX)
  euclid_apply (intersection_lines BC AX) as p
  euclid_apply (circle_points_between a x p α)
  euclid_apply (circle_line_intersections p b c BC α)
  euclid_apply (intersection_lines_opposing d y EF DY)
  euclid_apply (intersection_lines EF DY) as q
  euclid_apply (circle_points_between d y q β)
  euclid_apply (circle_line_intersections q e f EF β)
  euclid_apply (Elements.Book3.proposition_22_pair b a c x g BC AX α)
  euclid_apply (Elements.Book3.proposition_22_pair e d f y h EF DY β)
  euclid_finish

/--
A pentagon `ABCDE` in a circle with center `k`, with `AB = DE` and `BC = CD`, and `k`
within it: the circumferences `AB`, `DE` are equal, and `BC`, `CD` [Prop. 3.28]; adding
`BCD`, the whole `ABCD` is equal to the whole `EDCB`, and the angles `AED`, `BAE` on them
are equal.
-/
theorem proposition_11_angle : ∀ (a b c d e k : Point)
    (AB BC CD DE EA AC AD BD BE : Line) (α : Circle),
  k.isCentre α ∧ inscribedPentagon a b c d e α ∧ pentagon a b c d e AB BC CD DE EA ∧
  distinctPointsOnLine a c AC ∧ distinctPointsOnLine a d AD ∧
  distinctPointsOnLine b d BD ∧ distinctPointsOnLine b e BE ∧
  |(a─b)| = |(d─e)| ∧ |(b─c)| = |(c─d)| ∧
  k.sameSide c AB ∧ k.sameSide d BC ∧ k.sameSide e CD ∧ k.sameSide a DE ∧
  k.sameSide c AD ∧ k.sameSide d BE →
  ∠ a:e:d = ∠ e:a:b :=
by
  euclid_intros
  -- the circumferences AB, DE are equal, and BC, CD [Prop. 3.28]
  euclid_apply (point_on_circle_onlyif k a b α)
  euclid_apply (point_on_circle_onlyif k a d α)
  euclid_apply (point_on_circle_onlyif k a c α)
  euclid_apply (Elements.Book3.proposition_28 a b d e k k AB DE α α)
  euclid_apply (Elements.Book3.proposition_28 b c c d k k BC CD α α)
  -- ABCD is AB, BC, CD; and EDCB is ED, DC, CB (C.N. 2)
  euclid_apply (Elements.Book3.arc_add a d c e AD α)
  euclid_apply (Elements.Book3.arc_add a c b d AC α)
  euclid_apply (Elements.Book3.arc_add e b d a BE α)
  euclid_apply (Elements.Book3.arc_add d b c e BD α)
  euclid_apply (Elements.Book3.arc_side a b c k AB α)
  euclid_apply (Elements.Book3.arc_side b c a k BC α)
  euclid_apply (Elements.Book3.arc_side c d a k CD α)
  euclid_apply (Elements.Book3.arc_side e d b k DE α)
  euclid_apply (Elements.Book3.arc_side d c b k CD α)
  euclid_apply (Elements.Book3.arc_side c b d k BC α)
  have := Elements.Book3.arc_symm d e k α
  have := Elements.Book3.arc_symm c d k α
  have := Elements.Book3.arc_symm b c k α
  -- AED stands on ABCD, and BAE on EDCB [Prop. 3.27]
  euclid_apply (proposition_11_greater e a d a e b k k AD BE α α)
  euclid_finish

/--
The figure of Prop. 4.11: the triangle `ACD` in the circle, equiangular with the golden
triangle `FGH` [Props. 4.10, 4.2], its angles at `C`, `D` cut in half by `CE`, `DB`
[Prop. 1.9]. The five angles `DAC`, `ACE`, `ECD`, `CDB`, `BDA` are equal.
-/
theorem proposition_11_figure : ∀ (k : Point) (α : Circle),
  k.isCentre α →
  ∃ (a b c d e : Point) (AC CD AD : Line), formTriangle a c d AC CD AD ∧
  inscribedPentagon a b c d e α ∧ b.opposingSides d AC ∧ e.opposingSides c AD ∧
  ∠ a:c:e = ∠ d:a:c ∧ ∠ e:c:d = ∠ d:a:c ∧ ∠ c:d:b = ∠ d:a:c ∧ ∠ b:d:a = ∠ d:a:c ∧
  ∠ a:c:d = ∠ d:a:c + ∠ d:a:c ∧ ∠ c:d:a = ∠ d:a:c + ∠ d:a:c ∧
  ∠ d:a:c + ∠ d:a:c + ∠ d:a:c + ∠ d:a:c + ∠ d:a:c = ∟ + ∟ :=
by
  euclid_intros
  -- the isosceles triangle FGH with the angles at G, H double that at F [Prop. 4.10]
  euclid_apply arbitrary_point as f
  euclid_apply (distinct_points f) as g
  euclid_apply (line_from_points f g) as FG
  euclid_apply (proposition_10 f g FG) as (h, GH, HF)
  -- ACD in the circle, equiangular with FGH [Prop. 4.2]
  euclid_apply (proposition_2 f g h k FG GH HF α) as (a, c, d, AC, CD, AD)
  -- ACD, CDA cut in half by CE, DB [Prop. 1.9]
  euclid_apply (Elements.Book1.proposition_9 c a d AC CD) as x
  euclid_apply (Elements.Book1.proposition_9 d c a CD AD) as y
  euclid_apply (ray_meets_circle a c d x AC CD AD α) as e
  euclid_apply (ray_meets_circle c d a y CD AD AC α) as b
  euclid_apply (sum_angles_onlyif c a d x AC CD)
  euclid_apply (sum_angles_onlyif d c a y CD AD)
  euclid_apply (extend_point GH g h) as z
  euclid_apply (Elements.Book1.proposition_32 f g h z FG GH HF)
  use a, b, c, d, e, AC, CD, AD
  euclid_finish

/-- To inscribe an equilateral and equiangular pentagon `ABCDE` in a given circle `α`,
with center `k`; the center is within it, and on the far side of each diagonal from the
vertex the diagonal cuts off. -/
theorem proposition_11' : ∀ (k : Point) (α : Circle),
  k.isCentre α →
  ∃ (a b c d e : Point) (AB BC CD DE EA AC AD BD BE CE : Line),
  pentagon a b c d e AB BC CD DE EA ∧ inscribedPentagon a b c d e α ∧
  equilateralPentagon a b c d e ∧ equiangularPentagon a b c d e ∧
  distinctPointsOnLine a c AC ∧ distinctPointsOnLine a d AD ∧
  distinctPointsOnLine b d BD ∧ distinctPointsOnLine b e BE ∧
  distinctPointsOnLine c e CE ∧
  k.sameSide c AB ∧ k.sameSide d BC ∧ k.sameSide e CD ∧ k.sameSide a DE ∧
  k.sameSide b EA ∧ k.sameSide c AD ∧ k.sameSide d BE ∧ k.sameSide e AC ∧
  k.sameSide a BD ∧ k.sameSide b CE :=
by
  euclid_intros
  euclid_apply (proposition_11_figure k α) as (a, b, c, d, e, AC, CD, AD)
  -- let AB, BC, DE, EA be joined
  euclid_apply (line_from_points a b) as AB
  euclid_apply (line_from_points b c) as BC
  euclid_apply (line_from_points d e) as DE
  euclid_apply (line_from_points e a) as EA
  euclid_apply (pentagon_of_circle a b c d e AB BC CD DE EA AC AD α)
  -- Missed by Euclid: the five equal angles are less than right angles, and the center
  -- is on their sides of the circumferences they stand on [Props. 3.31, 3.31''].
  euclid_apply (centre_same_side_of_acute d c k a CD α)
  euclid_apply (centre_same_side_of_acute a e k c EA α)
  euclid_apply (centre_same_side_of_acute e d k c DE α)
  euclid_apply (centre_same_side_of_acute c b k d BC α)
  euclid_apply (centre_same_side_of_acute b a k d AB α)
  -- equal angles stand on equal circumferences [Prop. 3.26]: AB, BC, CD, DE, EA are
  -- equal, and so are the sides [Prop. 3.29]
  euclid_apply (point_on_circle_onlyif k a b α)
  euclid_apply (point_on_circle_onlyif k a c α)
  euclid_apply (point_on_circle_onlyif k a d α)
  euclid_apply (point_on_circle_onlyif k a e α)
  euclid_apply (Elements.Book3.proposition_26 c a e a d c k k EA CD α α)
  euclid_apply (Elements.Book3.proposition_26 c e d a d c k k DE CD α α)
  euclid_apply (Elements.Book3.proposition_26 d c b a d c k k BC CD α α)
  euclid_apply (Elements.Book3.proposition_26 d b a a d c k k AB CD α α)
  euclid_apply (Elements.Book3.arc_side d c a k CD α)
  euclid_apply (Elements.Book3.arc_side a e c k EA α)
  euclid_apply (Elements.Book3.arc_side e d c k DE α)
  euclid_apply (Elements.Book3.arc_side c b d k BC α)
  euclid_apply (Elements.Book3.arc_side b a d k AB α)
  euclid_apply (Elements.Book3.proposition_29 a e d c k k EA CD α α)
  euclid_apply (Elements.Book3.proposition_29 e d d c k k DE CD α α)
  euclid_apply (Elements.Book3.proposition_29 c b d c k k BC CD α α)
  euclid_apply (Elements.Book3.proposition_29 b a d c k k AB CD α α)
  euclid_assert equilateralPentagon a b c d e
  -- Missed by Euclid: the center is across each diagonal from the vertex it cuts off,
  -- the angles at the other vertices on that diagonal being less than right angles
  -- [Props. 3.21, 3.31''].
  euclid_apply (line_from_points b d) as BD
  euclid_apply (line_from_points b e) as BE
  euclid_apply (line_from_points c e) as CE
  euclid_apply (centre_same_side_of_acute a d k c AD α)
  euclid_apply (centre_same_side_of_acute c a k d AC α)
  euclid_apply (Elements.Book3.proposition_21 d a e c k EA α)
  euclid_apply (Elements.Book3.proposition_21 a c b d k BC α)
  euclid_apply (Elements.Book3.proposition_21 a e d c k DE α)
  euclid_apply (sum_angles_onlyif d b e a BD DE)
  euclid_apply (sum_angles_onlyif a d b c AD AB)
  euclid_apply (sum_angles_onlyif a e c d EA AC)
  euclid_apply (centre_same_side_of_acute b e k d BE α)
  euclid_apply (centre_same_side_of_acute d b k a BD α)
  euclid_apply (centre_same_side_of_acute e c k a CE α)
  -- the circumferences ABCD and EDCB are equal: BAE = AED [Prop. 3.27]; and so for the
  -- angles at B, C, D
  euclid_apply (proposition_11_angle a b c d e k AB BC CD DE EA AC AD BD BE α)
  euclid_apply (proposition_11_angle b c d e a k BC CD DE EA AB BD BE CE AC α)
  euclid_apply (proposition_11_angle c d e a b k CD DE EA AB BC CE AC AD BD α)
  euclid_apply (proposition_11_angle d e a b c k DE EA AB BC CD AD BD BE CE α)
  use a, b, c, d, e, AB, BC, CD, DE, EA, AC, AD, BD, BE, CE
  euclid_finish

/-- To inscribe an equilateral and equiangular pentagon `ABCDE` in a given circle `α`,
with center `k`. -/
theorem proposition_11 : ∀ (k : Point) (α : Circle),
  k.isCentre α →
  ∃ (a b c d e : Point) (AB BC CD DE EA : Line), pentagon a b c d e AB BC CD DE EA ∧
  inscribedPentagon a b c d e α ∧ equilateralPentagon a b c d e ∧
  equiangularPentagon a b c d e :=
by
  euclid_intros
  euclid_apply (proposition_11' k α) as (a, b, c, d, e, AB, BC, CD, DE, EA, AC, AD, BD,
    BE, CE)
  use a, b, c, d, e, AB, BC, CD, DE, EA

end Elements.Book4
