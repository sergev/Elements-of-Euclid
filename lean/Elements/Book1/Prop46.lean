import SystemE
import Elements.Book1.Prop03
import Elements.Book1.Prop11
import Elements.Book1.Prop29
import Elements.Book1.Prop31
import Elements.Book1.Prop34


namespace Elements.Book1

theorem proposition_46' : ∀ (a b x : Point) (AB : Line), ¬(x.onLine AB) ∧ distinctPointsOnLine a b AB →
  ∃ (d e : Point) (DE AD BE : Line), d.opposingSides x AB ∧ formParallelogram d e a b DE AB AD BE ∧
  |(d─e)| = |(a─b)| ∧ |(a─d)| = |(a─b)| ∧ |(b─e)| = |(a─b)| ∧
  (∠ b:a:d : ℝ) = ∟ ∧ (∠ a:d:e : ℝ) = ∟ ∧ (∠ a:b:e : ℝ) = ∟ ∧ (∠ b:e:d : ℝ) = ∟ :=
by
  euclid_intros
  euclid_apply (proposition_11_end_opposite a b x AB) as c'
  euclid_apply (line_from_points a c') as AC
  euclid_apply (extend_point_longer AC a c' (a─b)) as c
  euclid_apply (proposition_3 a c a b AC AB) as d
  euclid_apply (proposition_31 d a b AB) as DE
  euclid_apply (proposition_31 b a d AC) as BE
  euclid_apply (intersection_lines DE BE) as e
  euclid_apply (proposition_34' d e a b DE AB AC BE)
  euclid_apply (proposition_29_interior e b d a DE AB AC)
  use d, e, DE, AC, BE
  euclid_finish

theorem proposition_46 : ∀ (a b : Point) (AB : Line), distinctPointsOnLine a b AB →
  ∃ (d e : Point) (DE AD BE : Line), formParallelogram d e a b DE AB AD BE ∧
  |(d─e)| = |(a─b)| ∧ |(a─d)| = |(a─b)| ∧ |(b─e)| = |(a─b)| ∧
  (∠ b:a:d = ∟) ∧ (∠ a:d:e = ∟) ∧ (∠ a:b:e = ∟) ∧ (∠ b:e:d = ∟) :=
by
  euclid_intros
  euclid_apply (proposition_1 a b AB) as x
  euclid_apply (proposition_46' a b x AB) as (d, e, DE, AD, BE)
  use d, e, DE, AD, BE

end Elements.Book1
