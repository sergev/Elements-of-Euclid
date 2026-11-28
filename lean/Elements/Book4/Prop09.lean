import SystemE
import Elements.Book1.Prop06
import Elements.Book1.Prop08
import Elements.Book4.Lemmas

namespace Elements.Book4

/-- To circumscribe a circle `α`, with center `e`, about a given square `ABCD`. -/
theorem proposition_9 : ∀ (a b c d : Point) (AB BC CD DA : Line),
  square a b c d AB BC CD DA →
  ∃ (e : Point) (α : Circle), e.isCentre α ∧ inscribedQuadrilateral a b c d α :=
by
  euclid_intros
  -- AC and BD joined cut one another at E
  euclid_apply (line_from_points a c) as AC
  euclid_apply (line_from_points b d) as BD
  euclid_apply (intersection_lines_opposing b d AC BD)
  euclid_apply (intersection_lines AC BD) as e
  euclid_assert between a e c
  euclid_assert between b e d
  -- DA = AB, AC common, DC = BC: DAC = BAC [Prop. 1.8]; DAB is cut in half by AC, and
  -- similarly the angles at B, C, D
  euclid_apply (Elements.Book1.proposition_8 a d c a b c DA CD AC AB BC AC)
  euclid_apply (Elements.Book1.proposition_8 b a d b c d AB DA BD BC CD BD)
  euclid_apply (Elements.Book1.proposition_8 c b a c d a BC AB AC CD DA AC)
  euclid_apply (Elements.Book1.proposition_8 d c b d a b CD BC BD DA AB BD)
  euclid_apply (sum_angles_onlyif a d b c DA AB)
  euclid_apply (sum_angles_onlyif b a c d AB BC)
  euclid_apply (sum_angles_onlyif c b d a BC CD)
  euclid_apply (sum_angles_onlyif d c a b CD DA)
  -- EAB, EBA are halves of equal angles: EA = EB [Prop. 1.6]; and similarly EB = EC,
  -- EC = ED
  euclid_apply (equal_angles a c e b b AC AB)
  euclid_apply (equal_angles b d e a a BD AB)
  euclid_apply (equal_angles b d e c c BD BC)
  euclid_apply (equal_angles c a e b b AC BC)
  euclid_apply (equal_angles c a e d d AC CD)
  euclid_apply (equal_angles d b e c c BD CD)
  euclid_apply (Elements.Book1.proposition_6 e a b AC AB BD)
  euclid_apply (Elements.Book1.proposition_6 e b c BD BC AC)
  euclid_apply (Elements.Book1.proposition_6 e c d AC CD BD)
  -- the circle with center E and radius EA goes through B, C, D
  euclid_apply (circle_from_points e a) as α
  euclid_apply (point_on_circle_if e a b α)
  euclid_apply (point_on_circle_if e a c α)
  euclid_apply (point_on_circle_if e a d α)
  use e, α

end Elements.Book4
