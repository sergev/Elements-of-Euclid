import SystemE
import Elements.Book1.Prop17
import Elements.Book1.Prop47
import Elements.Book2.Prop04

namespace Elements.Book2

open Elements.Book1

theorem proposition_12 : ∀ (a b c d : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (∠ b:a:c : ℝ) > ∟ ∧
  d.onLine AC ∧ d ≠ a ∧ (∠ b:d:a : ℝ) = ∟ →
  |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| + 2 * (|(c─a)| * |(a─d)|) :=
by
  euclid_intros
  -- Missed by Euclid: the perpendicular falls on CA produced, beyond A,
  -- else a triangle would have an obtuse and a right angle [Prop. 1.17].
  have : between c a d := by
    by_contra hn
    by_cases hdc : d = c
    · subst hdc
      euclid_apply (proposition_17 b a d AB AC BC)
      euclid_finish
    · euclid_apply (line_from_points b d) as BD
      euclid_apply (equal_angles a b b c d AB AC)
      euclid_apply (proposition_17 b a d AB AC BD)
      euclid_finish
  euclid_apply (line_from_points b d) as BD
  -- CD is cut at A [Prop. 2.4]
  euclid_apply (Elements.Book2.proposition_4 c d a)
  -- the angle at D is right [Prop. 1.47]
  euclid_apply (proposition_47 d c b AC BC BD)
  euclid_apply (proposition_47 d a b AC AB BD)
  euclid_finish

end Elements.Book2
