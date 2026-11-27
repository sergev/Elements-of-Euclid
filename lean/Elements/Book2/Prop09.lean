import SystemE
import Elements.Book1.Prop03
import Elements.Book1.Prop05
import Elements.Book1.Prop06
import Elements.Book1.Prop11
import Elements.Book1.Prop29
import Elements.Book1.Prop31
import Elements.Book1.Prop32
import Elements.Book1.Prop34
import Elements.Book1.Prop47

namespace Elements.Book2

open Elements.Book1

theorem proposition_9 : ∀ (a b c d : Point),
  between a c b ∧ between c d b ∧ |(a─c)| = |(c─b)| →
  |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| = 2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|) :=
by
  euclid_intros
  euclid_apply (line_from_points a b) as AB
  euclid_apply (proposition_11 a b c AB) as e'
  euclid_apply (line_from_points c e') as CE
  euclid_apply (extend_point_longer CE c e' (a─c)) as x
  euclid_apply (proposition_3 c x a c CE AB) as e
  euclid_apply (line_from_points e a) as EA
  euclid_apply (line_from_points e b) as EB
  euclid_apply (proposition_31 d c e CE) as DF
  euclid_apply (intersection_lines DF EB) as f
  euclid_apply (proposition_31 f a b AB) as FG
  euclid_apply (intersection_lines FG CE) as g
  euclid_apply (line_from_points a f) as AF
  -- CEA, CAE, CEB, EBC are each half a right-angle; so AEB is right
  euclid_apply (proposition_5' c a e AB EA CE)
  euclid_apply (proposition_32 e a c b EA AB CE)
  euclid_apply (proposition_5' c b e AB EB CE)
  euclid_apply (proposition_32 e b c a EB AB CE)
  -- EGF is right, so EG = GF
  euclid_apply (proposition_29_exterior f b e g c FG AB CE)
  euclid_apply (proposition_32 f e g c EB CE FG)
  euclid_apply (Elements.Book1.proposition_6 g e f CE EB FG)
  -- FDB is right, so FD = DB
  euclid_apply (proposition_29_exterior f e b d c DF CE AB)
  euclid_apply (proposition_32 f b d c EB AB DF)
  euclid_apply (Elements.Book1.proposition_6 d f b DF EB AB)
  euclid_apply (proposition_34' g f c d FG AB CE DF)
  -- the squares [Prop. 1.47]
  euclid_apply (proposition_47 c a e AB EA CE)
  euclid_apply (proposition_47 g e f CE EB FG)
  euclid_apply (proposition_47 e a f EA AF EB)
  euclid_apply (proposition_47 d a f AB AF DF)
  euclid_finish

end Elements.Book2
