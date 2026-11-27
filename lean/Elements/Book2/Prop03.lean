import SystemE
import Elements.Book1.Prop29
import Elements.Book1.Prop30
import Elements.Book1.Prop31
import Elements.Book1.Prop34
import Elements.Book1.Prop46

namespace Elements.Book2

open Elements.Book1

theorem proposition_3 : ∀ (a b c : Point),
  between a c b →
  |(a─b)| * |(b─c)| = |(a─c)| * |(c─b)| + |(b─c)| * |(b─c)| :=
by
  euclid_intros
  euclid_apply (line_from_points a b) as AB
  euclid_apply (proposition_46 c b AB) as (d, e, DE, CD, BE)
  euclid_apply (proposition_31 a c d CD) as AF
  euclid_apply (intersection_lines AF DE) as f
  -- Missed by Euclid.
  euclid_apply (proposition_30 AF BE CD)
  euclid_apply (proposition_29_interior d f c a CD AF AB)
  euclid_apply (proposition_34' f d a c DE AB AF CD)
  euclid_apply (proposition_34' f e a b DE AB AF BE)
  euclid_apply (rectangle_area f d a c DE AB AF CD)
  euclid_apply (rectangle_area f e a b DE AB AF BE)
  euclid_apply (rectangle_area d e c b DE AB CD BE)
  euclid_apply (sum_parallelograms_area f e a b d c DE AB AF BE)
  euclid_assert Triangle.area △ f:a:b + Triangle.area △ f:e:b = |(a─b)| * |(b─c)|
  euclid_assert Triangle.area △ f:a:c + Triangle.area △ f:d:c = |(a─c)| * |(c─b)|
  euclid_assert Triangle.area △ d:c:b + Triangle.area △ d:e:b = |(b─c)| * |(b─c)|
  euclid_assert Triangle.area △ f:a:b + Triangle.area △ f:e:b =
    (Triangle.area △ f:a:c + Triangle.area △ f:d:c) + (Triangle.area △ d:c:b + Triangle.area △ d:e:b)
  euclid_finish

end Elements.Book2
