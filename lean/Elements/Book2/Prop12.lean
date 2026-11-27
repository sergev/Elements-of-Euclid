import SystemE
import Elements.Book1.Prop47
import Elements.Book2.Prop04

namespace Elements.Book2

open Elements.Book1

theorem proposition_12 : ∀ (a b c d : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (∠ b:a:c : ℝ) > ∟ ∧ between c a d ∧ (∠ b:d:a : ℝ) = ∟ →
  |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| + 2 * (|(c─a)| * |(a─d)|) :=
by
  euclid_intros
  euclid_apply (line_from_points b d) as BD
  -- CD is cut at A [Prop. 2.4]
  euclid_apply (Elements.Book2.proposition_4 c d a)
  -- the angle at D is right [Prop. 1.47]
  euclid_apply (proposition_47 d c b AC BC BD)
  euclid_apply (proposition_47 d a b AC AB BD)
  euclid_finish

end Elements.Book2
