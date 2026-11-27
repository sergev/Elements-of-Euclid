import SystemE
import Elements.Book1.Prop03
import Elements.Book1.Prop05
import Elements.Book1.Prop06
import Elements.Book1.Prop11
import Elements.Book1.Prop15
import Elements.Book1.Prop29
import Elements.Book1.Prop31
import Elements.Book1.Prop32
import Elements.Book1.Prop34
import Elements.Book1.Prop47

namespace Elements.Book2

open Elements.Book1

theorem proposition_10 : ∀ (a b c d : Point),
  between a c b ∧ between c b d ∧ |(a─c)| = |(c─b)| →
  |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| = 2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|) :=
by
  euclid_intros
  euclid_apply (line_from_points a d) as AB
  euclid_apply (proposition_11 a d c AB) as e'
  euclid_apply (line_from_points c e') as CE
  euclid_apply (extend_point_longer CE c e' (a─c)) as x
  euclid_apply (proposition_3 c x a c CE AB) as e
  euclid_apply (line_from_points e a) as EA
  euclid_apply (line_from_points e b) as EB
  euclid_apply (proposition_31 e a d AB) as EF
  euclid_apply (proposition_31 d c e CE) as FD
  euclid_apply (intersection_lines EF FD) as f
  -- EB and FD meet [Post. 5]
  euclid_apply (proposition_29_interior c d e f CE FD EF)
  euclid_apply (lines_intersect b e f d EB EF FD) as g
  euclid_apply (line_from_points a g) as AG
  -- CEA, CAE, CEB, EBC are each half a right-angle; so AEB is right
  euclid_apply (proposition_5' c a e AB EA CE)
  euclid_apply (proposition_32 e a c b EA AB CE)
  euclid_apply (proposition_5' c b e AB EB CE)
  euclid_apply (proposition_32 e b c a EB AB CE)
  -- DBG is half a right-angle and BDG is right, so BD = DG
  euclid_apply (proposition_15 c d g e b AB EB)
  euclid_apply (proposition_29_alternate e g c d CE FD AB)
  euclid_apply (proposition_32 g d b c FD AB EB)
  euclid_apply (Elements.Book1.proposition_6 d b g AB EB FD)
  -- EFG is right, so GF = EF
  euclid_apply (proposition_34' e f c d EF AB CE FD)
  euclid_apply (extend_point EB e g) as y
  euclid_apply (proposition_32 f e g y EF EB FD)
  euclid_apply (Elements.Book1.proposition_6 f e g EF EB FD)
  -- the squares [Prop. 1.47]
  euclid_apply (proposition_47 c a e AB EA CE)
  euclid_apply (proposition_47 f e g EF EB FD)
  euclid_apply (proposition_47 e a g EA AG EB)
  euclid_apply (proposition_47 d a g AB AG FD)
  euclid_finish

end Elements.Book2
