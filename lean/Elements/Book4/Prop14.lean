import SystemE
import Elements.Book1.Prop06
import Elements.Book4.Prop13

namespace Elements.Book4

/-- To circumscribe a circle `α`, with center `f`, about a given equilateral and
equiangular pentagon `ABCDE`. -/
theorem proposition_14 : ∀ (a b c d e : Point) (AB BC CD DE EA : Line),
  pentagon a b c d e AB BC CD DE EA ∧ equilateralPentagon a b c d e ∧
  equiangularPentagon a b c d e →
  ∃ (f : Point) (α : Circle), f.isCentre α ∧ inscribedPentagon a b c d e α :=
by
  euclid_intros
  -- the angles at C, D cut in half by CF, DF, and so those at B, A, E by FB, FA, FE, as
  -- in the proposition before
  euclid_apply (proposition_13_centre a b c d e AB BC CD DE EA) as f
  -- FCD, half of BCD, is equal to FDC, half of CDE: FC = FD [Prop. 1.6]; and so FB, FA,
  -- FE
  euclid_apply (line_from_points f a) as FA
  euclid_apply (line_from_points f b) as FB
  euclid_apply (line_from_points f c) as FC
  euclid_apply (line_from_points f d) as FD
  euclid_apply (line_from_points f e) as FE
  euclid_apply (Elements.Book1.proposition_6 f c d FC CD FD)
  euclid_apply (Elements.Book1.proposition_6 f b c FB BC FC)
  euclid_apply (Elements.Book1.proposition_6 f a b FA AB FB)
  euclid_apply (Elements.Book1.proposition_6 f e a FE EA FA)
  -- the circle with center F and radius FA goes through B, C, D, E
  euclid_apply (circle_from_points f a) as α
  euclid_apply (point_on_circle_if f a b α)
  euclid_apply (point_on_circle_if f a c α)
  euclid_apply (point_on_circle_if f a d α)
  euclid_apply (point_on_circle_if f a e α)
  use f, α

end Elements.Book4
