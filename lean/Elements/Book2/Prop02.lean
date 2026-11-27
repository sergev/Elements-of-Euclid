import SystemE
import Elements.Book1.Prop29
import Elements.Book1.Prop30
import Elements.Book1.Prop31
import Elements.Book1.Prop34
import Elements.Book1.Prop46

namespace Elements.Book2

open Elements.Book1

theorem proposition_2 : ∀ (a b c : Point),
  between a c b →
  |(a─b)| * |(b─c)| + |(b─a)| * |(a─c)| = |(a─b)| * |(a─b)| :=
by
  euclid_intros
  euclid_apply (line_from_points a b) as AB
  euclid_apply (proposition_46 a b AB) as (d, e, DE, AD, BE)
  euclid_apply (proposition_31 c a d AD) as CF
  euclid_apply (intersection_lines CF DE) as f
  -- Missed by Euclid.
  euclid_apply (proposition_30 CF BE AD)
  euclid_apply (proposition_29_interior d f a c AD CF AB)
  euclid_apply (proposition_34' d f a c DE AB AD CF)
  euclid_apply (proposition_34' f e c b DE AB CF BE)
  euclid_apply (rectangle_area d e a b DE AB AD BE)
  euclid_apply (rectangle_area d f a c DE AB AD CF)
  euclid_apply (rectangle_area f e c b DE AB CF BE)
  euclid_apply (sum_parallelograms_area d e a b f c DE AB AD BE)
  euclid_assert Triangle.area △ d:a:b + Triangle.area △ d:e:b = |(a─b)| * |(a─b)|
  euclid_assert Triangle.area △ d:a:c + Triangle.area △ d:f:c = |(b─a)| * |(a─c)|
  euclid_assert Triangle.area △ f:c:b + Triangle.area △ f:e:b = |(a─b)| * |(b─c)|
  euclid_assert Triangle.area △ d:a:b + Triangle.area △ d:e:b =
    (Triangle.area △ d:a:c + Triangle.area △ d:f:c) + (Triangle.area △ f:c:b + Triangle.area △ f:e:b)
  euclid_finish

end Elements.Book2
