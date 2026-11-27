import SystemE
import Elements.Book1.Prop03
import Elements.Book1.Prop08
import Elements.Book1.Prop11
import Elements.Book1.Prop47

namespace Elements.Book1

theorem proposition_48 : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| →
  ∠ b:a:c = ∟ :=
by
  euclid_intros
  euclid_apply (proposition_11_end a c AC) as d'
  euclid_apply (line_from_points a d') as AD
  euclid_apply (extend_point AD d' a) as d''
  euclid_apply (extend_point_longer AD d'' a (a─b)) as d'''
  euclid_apply (proposition_3 a d''' a b AD AB) as d
  euclid_apply (line_from_points d c) as DC
  have hda : |(d─a)| = |(a─b)| := by euclid_finish
  have : |(d─a)| * |(d─a)| = |(a─b)| * |(a─b)| := by rw [hda]
  have : |(b─a)| * |(b─a)| = |(a─b)| * |(a─b)| := by rw [segment_symmetric b a]
  euclid_apply (proposition_47 a d c AD DC AC)
  have : |(d─c)| * |(d─c)| = |(b─c)| * |(b─c)| := by linarith
  have : |(d─c)| = |(b─c)| := (mul_self_inj (segment_gte_zero _) (segment_gte_zero _)).1 this
  euclid_apply (proposition_8 a b c a d c AB BC AC AD DC AC)
  euclid_apply (equal_angles a d' d c c AD AC)
  euclid_finish

end Elements.Book1
