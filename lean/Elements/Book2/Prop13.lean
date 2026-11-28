import SystemE
import Elements.Book1.Prop47
import Elements.Book2.Prop07

namespace Elements.Book2

open Elements.Book1

theorem proposition_13 : ∀ (a b c d : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (∠ a:b:c : ℝ) < ∟ ∧ between b d c ∧ (∠ a:d:b : ℝ) = ∟ →
  |(a─c)| * |(a─c)| + 2 * (|(c─b)| * |(b─d)|) = |(c─b)| * |(c─b)| + |(b─a)| * |(b─a)| :=
by
  euclid_intros
  euclid_apply (line_from_points a d) as AD
  -- CB is cut at D [Prop. 2.7]
  euclid_apply (Elements.Book2.proposition_7 c b d)
  -- the angle at D is right [Prop. 1.47]
  euclid_apply (proposition_47 d b a BC AB AD)
  euclid_apply (right_angle_on_lines a d b a c AD BC)
  euclid_apply (proposition_47 d a c AD AC BC)
  euclid_finish

end Elements.Book2
