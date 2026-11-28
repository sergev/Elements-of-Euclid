import SystemE
import Elements.Book1.Prop05
import Elements.Book1.Prop11
import Elements.Book1.Prop13
import Elements.Book1.Prop15
import Elements.Book1.Prop32
import Elements.Book3.Prop26
import Elements.Book3.Prop29
import Elements.Book4.Lemmas
import Elements.Book4.Prop11

namespace Elements.Book4

/--
Six points of a circle, with the diameters `AD`, `BE`, `CF` cutting one another at the
center `g`, and `B`, `C` on one side of `AD`, `C`, `D` of `BE`, `D`, `E` of `CF`, make a
convex hexagon: each four with a diameter for a diagonal make a convex quadrilateral.
-/
theorem proposition_15_hexagon : ∀ (a b c d e f g : Point)
    (AB BC CD DE EF FA AD BE CF : Line) (α : Circle),
  inscribedHexagon a b c d e f α ∧ distinctPointsOnLine a b AB ∧
  distinctPointsOnLine b c BC ∧ distinctPointsOnLine c d CD ∧
  distinctPointsOnLine d e DE ∧ distinctPointsOnLine e f EF ∧
  distinctPointsOnLine f a FA ∧ distinctPointsOnLine a d AD ∧
  distinctPointsOnLine b e BE ∧ distinctPointsOnLine c f CF ∧
  between a g d ∧ between b g e ∧ between c g f ∧
  b.sameSide c AD ∧ c.sameSide d BE ∧ d.sameSide e CF →
  hexagon a b c d e f AB BC CD DE EF FA :=
by
  euclid_intros
  euclid_apply (line_from_points a c) as AC
  euclid_apply (line_from_points b d) as BD
  euclid_apply (line_from_points c e) as CE
  euclid_apply (line_from_points d f) as DF
  euclid_apply (line_from_points e a) as EA
  euclid_apply (line_from_points f b) as FB
  euclid_apply (quadrilateral_of_circle a b d e AB BD DE EA AD α)
  euclid_apply (quadrilateral_of_circle b c e f BC CE EF FB BE α)
  euclid_apply (quadrilateral_of_circle c d f a CD DF FA AC CF α)
  euclid_apply (quadrilateral_of_circle a b d f AB BD DF FA AD α)
  euclid_apply (quadrilateral_of_circle b c e a BC CE EA AB BE α)
  euclid_apply (quadrilateral_of_circle c d f b CD DF FB BC CF α)
  euclid_apply (quadrilateral_of_circle d e a c DE EA AC CD AD α)
  euclid_apply (quadrilateral_of_circle e f b d EF FB BD DE BE α)
  euclid_apply (quadrilateral_of_circle f a c e FA AC CE EF CF α)
  euclid_finish

/--
A hexagon `ABCDEF` in a circle with center `g` on the diameters `AD`, `BE`, `CF`, with
`FA = ED`: the circumferences `FA`, `ED` are equal [Prop. 3.28]; adding `ABCD`, the whole
`FABCD` is equal to the whole `EDCBA`, and the angles `FED`, `AFE` on them are equal.
-/
theorem proposition_15_angle : ∀ (a b c d e f g : Point)
    (AB BC CD DE EF FA AD BE CF : Line) (α : Circle),
  g.isCentre α ∧ inscribedHexagon a b c d e f α ∧ hexagon a b c d e f AB BC CD DE EF FA ∧
  distinctPointsOnLine a d AD ∧ distinctPointsOnLine b e BE ∧
  distinctPointsOnLine c f CF ∧ between a g d ∧ between b g e ∧ between c g f ∧
  |(f─a)| = |(d─e)| →
  ∠ d:e:f = ∠ e:f:a :=
by
  euclid_intros
  euclid_apply (line_from_points a c) as AC
  euclid_apply (line_from_points b d) as BD
  euclid_apply (line_from_points d f) as DF
  euclid_apply (line_from_points a e) as AE
  -- the circumferences FA, ED are equal [Prop. 3.28]
  euclid_apply (point_on_circle_onlyif g a d α)
  euclid_apply (point_on_circle_onlyif g a f α)
  euclid_apply (Elements.Book3.proposition_28 f a d e g g FA DE α α)
  -- FABCD is FA, AB, BC, CD; and EDCBA is ED, DC, CB, BA (C.N. 2)
  euclid_apply (Elements.Book3.arc_add d f c e DF α)
  euclid_apply (Elements.Book3.arc_add c f a d CF α)
  euclid_apply (Elements.Book3.arc_add c a b f AC α)
  euclid_apply (Elements.Book3.arc_add a e d f AE α)
  euclid_apply (Elements.Book3.arc_add a d b e AD α)
  euclid_apply (Elements.Book3.arc_add b d c a BD α)
  euclid_apply (Elements.Book3.arc_side d c f g CD α)
  euclid_apply (Elements.Book3.arc_side a f c g FA α)
  euclid_apply (Elements.Book3.arc_side c b a g BC α)
  euclid_apply (Elements.Book3.arc_side b a c g AB α)
  euclid_apply (Elements.Book3.arc_side d e a g DE α)
  euclid_apply (Elements.Book3.arc_side a b d g AB α)
  euclid_apply (Elements.Book3.arc_side b c d g BC α)
  euclid_apply (Elements.Book3.arc_side c d b g CD α)
  have := Elements.Book3.arc_symm c d g α
  have := Elements.Book3.arc_symm b c g α
  have := Elements.Book3.arc_symm a b g α
  have := Elements.Book3.arc_symm a f g α
  -- FED stands on FABCD, and AFE on EDCBA [Prop. 3.27]
  euclid_apply (proposition_11_greater e d f f a e g g DF AE α α)
  euclid_finish

/-- To inscribe an equilateral and equiangular hexagon `ABCDEF` in a given circle `α`,
with center `g`; its side is equal to the radius. -/
theorem proposition_15' : ∀ (g : Point) (α : Circle),
  g.isCentre α →
  ∃ (a b c d e f : Point) (AB BC CD DE EF FA : Line),
  hexagon a b c d e f AB BC CD DE EF FA ∧ inscribedHexagon a b c d e f α ∧
  equilateralHexagon a b c d e f ∧ equiangularHexagon a b c d e f ∧ |(a─b)| = |(g─a)| :=
by
  euclid_intros
  -- the diameter AD; the circle EGCH with center D and radius DG
  euclid_apply (exists_point_on_circle α) as a
  euclid_apply (line_from_points a g) as AD
  euclid_apply (intersection_circle_line_extending_points α AD g a) as d
  euclid_apply (circle_from_points d g) as EGCH
  euclid_apply (intersection_circle_circle_2 d g α EGCH)
  euclid_apply (Elements.Book1.proposition_11 a d g AD) as x
  euclid_apply (intersection_same_side α EGCH x g d AD) as e
  euclid_apply (intersection_opposite_side α EGCH x g d AD) as c
  -- EG, CG drawn across to B, F
  euclid_apply (line_from_points e g) as BE
  euclid_apply (line_from_points c g) as CF
  euclid_apply (intersection_circle_line_extending_points α BE g e) as b
  euclid_apply (intersection_circle_line_extending_points α CF g c) as f
  -- GE = GD and DE = DG: EGD is equilateral, and its angles are each a third of two
  -- right angles [Props. 1.5, 1.32]; and so DGC
  euclid_apply (point_on_circle_onlyif g a d α)
  euclid_apply (point_on_circle_onlyif g a e α)
  euclid_apply (point_on_circle_onlyif g a c α)
  euclid_apply (point_on_circle_onlyif d g e EGCH)
  euclid_apply (point_on_circle_onlyif d g c EGCH)
  euclid_apply (line_from_points d e) as DE
  euclid_apply (line_from_points c d) as CD
  euclid_apply (Elements.Book1.proposition_5' g e d BE DE AD)
  euclid_apply (Elements.Book1.proposition_5' d e g DE BE AD)
  euclid_apply (Elements.Book1.proposition_5' g c d CF CD AD)
  euclid_apply (Elements.Book1.proposition_5' d c g CD CF AD)
  euclid_apply (Elements.Book1.proposition_32 e d g a DE AD BE)
  euclid_apply (Elements.Book1.proposition_32 c d g a CD AD CF)
  -- Missed by Euclid: D is within the angle EGC; else A would be, and EGC, made of the
  -- remainders of EGD and DGC, would be greater than two right angles [Prop. 1.13].
  have : d.sameSide c BE ∧ d.sameSide e CF := by
    by_cases (d.sameSide c BE)
    · euclid_apply (triple_incidence_2 BE AD CF g e d c)
      euclid_finish
    · exfalso
      euclid_apply (Elements.Book1.proposition_13 e g d a BE AD)
      euclid_apply (Elements.Book1.proposition_13 c g d a CF AD)
      euclid_apply (triple_incidence_2 CF AD BE g c a e)
      euclid_apply (sum_angles_onlyif g e c a BE CF)
      have := (angle_range (Angle.ofPoints e g c)).2
      euclid_finish
  -- CG standing on EB makes EGC, CGB equal to two right angles [Prop. 1.13]: CGB is a
  -- third of two right angles; and the vertical angles BGA, AGF, FGE are equal to EGD,
  -- DGC, CGB [Prop. 1.15]
  euclid_apply (sum_angles_onlyif g e c d BE CF)
  euclid_apply (Elements.Book1.proposition_13 c g e b CF BE)
  euclid_apply (Elements.Book1.proposition_15 b e a d g BE AD)
  euclid_apply (Elements.Book1.proposition_15 a d c f g AD CF)
  euclid_apply (Elements.Book1.proposition_15 c f b e g CF BE)
  -- the six angles at G being equal, so are the circumferences on them [Prop. 3.26],
  -- and the straight lines under these [Prop. 3.29]
  euclid_apply (line_from_points a b) as AB
  euclid_apply (line_from_points b c) as BC
  euclid_apply (line_from_points e f) as EF
  euclid_apply (line_from_points f a) as FA
  euclid_apply (point_on_circle_onlyif g a b α)
  euclid_apply (point_on_circle_onlyif g a f α)
  euclid_apply (Elements.Book3.proposition_26' a b d e g g AB DE α α)
  euclid_apply (Elements.Book3.proposition_26' b c d e g g BC DE α α)
  euclid_apply (Elements.Book3.proposition_26' c d d e g g CD DE α α)
  euclid_apply (Elements.Book3.proposition_26' e f d e g g EF DE α α)
  euclid_apply (Elements.Book3.proposition_26' f a d e g g FA DE α α)
  euclid_apply (Elements.Book3.proposition_29 a b d e g g AB DE α α)
  euclid_apply (Elements.Book3.proposition_29 b c d e g g BC DE α α)
  euclid_apply (Elements.Book3.proposition_29 c d d e g g CD DE α α)
  euclid_apply (Elements.Book3.proposition_29 e f d e g g EF DE α α)
  euclid_apply (Elements.Book3.proposition_29 f a d e g g FA DE α α)
  -- Missed by Euclid: ABCDEF is convex.
  euclid_apply (proposition_15_hexagon a b c d e f g AB BC CD DE EF FA AD BE CF α)
  -- FA = ED; adding ABCD, FED = AFE [Prop. 3.27]; and so the other angles
  euclid_apply (proposition_15_angle a b c d e f g AB BC CD DE EF FA AD BE CF α)
  euclid_apply (proposition_15_angle b c d e f a g BC CD DE EF FA AB BE CF AD α)
  euclid_apply (proposition_15_angle c d e f a b g CD DE EF FA AB BC CF AD BE α)
  euclid_apply (proposition_15_angle d e f a b c g DE EF FA AB BC CD AD BE CF α)
  euclid_apply (proposition_15_angle e f a b c d g EF FA AB BC CD DE BE CF AD α)
  use a, b, c, d, e, f, AB, BC, CD, DE, EF, FA
  euclid_finish

/-- To inscribe an equilateral and equiangular hexagon `ABCDEF` in a given circle `α`,
with center `g`. -/
theorem proposition_15 : ∀ (g : Point) (α : Circle),
  g.isCentre α →
  ∃ (a b c d e f : Point) (AB BC CD DE EF FA : Line),
  hexagon a b c d e f AB BC CD DE EF FA ∧ inscribedHexagon a b c d e f α ∧
  equilateralHexagon a b c d e f ∧ equiangularHexagon a b c d e f :=
by
  euclid_intros
  euclid_apply (proposition_15' g α) as (a, b, c, d, e, f, AB, BC, CD, DE, EF, FA)
  use a, b, c, d, e, f, AB, BC, CD, DE, EF, FA

/-- Corollary: the side of the hexagon is equal to the radius of the circle. -/
theorem proposition_15_corollary : ∀ (g : Point) (α : Circle),
  g.isCentre α →
  ∃ (a b c d e f : Point) (AB BC CD DE EF FA : Line),
  hexagon a b c d e f AB BC CD DE EF FA ∧ inscribedHexagon a b c d e f α ∧
  equilateralHexagon a b c d e f ∧ |(a─b)| = |(g─a)| :=
by
  euclid_intros
  euclid_apply (proposition_15' g α) as (a, b, c, d, e, f, AB, BC, CD, DE, EF, FA)
  use a, b, c, d, e, f, AB, BC, CD, DE, EF, FA

/-
Euclid's further remarks, that a hexagon can be circumscribed about a circle, and a
circle inscribed in and circumscribed about a given hexagon, "similarly to the pentagon",
are given without proof, and are left out.
-/

end Elements.Book4
