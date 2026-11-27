import SystemE
import Elements.Book1.Prop05
import Elements.Book1.Prop06
import Elements.Book1.Prop29
import Elements.Book1.Prop30
import Elements.Book1.Prop31
import Elements.Book1.Prop34
import Elements.Book1.Prop43
import Elements.Book1.Prop46

namespace Elements.Book2

open Elements.Book1

theorem proposition_7 : ∀ (a b c : Point),
  between a c b →
  |(a─b)| * |(a─b)| + |(b─c)| * |(b─c)| = 2 * (|(a─b)| * |(b─c)|) + |(c─a)| * |(c─a)| :=
by
  euclid_intros
  euclid_apply (line_from_points a b) as AB
  euclid_apply (proposition_46 a b AB) as (d, e, DE, AD, BE)
  euclid_apply (line_from_points b d) as BD
  euclid_apply (proposition_31 c a d AD) as CF
  euclid_apply (intersection_lines CF BD) as g
  euclid_apply (intersection_lines CF DE) as f
  euclid_apply (proposition_31 g a b AB) as HK
  euclid_apply (intersection_lines HK AD) as h
  euclid_apply (intersection_lines HK BE) as k
  -- Missed by Euclid.
  euclid_apply (proposition_30 CF BE AD)
  euclid_apply (proposition_30 HK DE AB)
  -- CGKB is a square
  euclid_apply (proposition_29_exterior c a b g d CF AD BD)
  euclid_apply (proposition_5' a d b AD BD AB)
  euclid_apply (proposition_6 c g b CF BD AB)
  euclid_apply (proposition_34' g k c b HK AB CF BE)
  euclid_apply (proposition_29_interior d g a c AD CF AB)
  euclid_apply (rectangle_area g k c b HK AB CF BE)
  euclid_assert Triangle.area △ g:c:b + Triangle.area △ g:k:b = |(c─b)| * |(c─b)|
  -- HF is a square on AC
  euclid_apply (proposition_34' h g a c HK AB AD CF)
  euclid_apply (proposition_34' d f h g DE HK AD CF)
  euclid_apply (proposition_29_interior b g a h AB HK AD)
  euclid_apply (rectangle_area d f h g DE HK AD CF)
  euclid_assert Triangle.area △ d:h:g + Triangle.area △ d:f:g = |(a─c)| * |(a─c)|
  -- AG = GE; add CK: AK = CE
  euclid_apply (rectangle_area h g a c HK AB AD CF)
  euclid_apply (proposition_43 b e d a k h f c g AB DE BE AD BD HK CF)
  euclid_apply (sum_parallelograms_area h k a b g c HK AB AD BE)
  euclid_apply (sum_parallelograms_area f c e b g k CF BE DE AB)
  euclid_assert Triangle.area △ h:a:b + Triangle.area △ h:k:b = Triangle.area △ f:c:b + Triangle.area △ f:e:b
  -- AK is the rectangle on AB, BC
  euclid_apply (proposition_34' h k a b HK AB AD BE)
  euclid_apply (rectangle_area h k a b HK AB AD BE)
  euclid_assert Triangle.area △ h:a:b + Triangle.area △ h:k:b = |(a─b)| * |(b─c)|
  -- the gnomon and CK are twice AK; add HF, the square on AC
  euclid_assert (Triangle.area △ h:a:c + Triangle.area △ h:g:c) + (Triangle.area △ g:c:b + Triangle.area △ g:k:b) +
    (Triangle.area △ k:e:f + Triangle.area △ k:f:g) + (Triangle.area △ g:c:b + Triangle.area △ g:k:b) =
    2 * (Triangle.area △ h:a:b + Triangle.area △ h:k:b)
  euclid_apply (rectangle_area d e a b DE AB AD BE)
  euclid_apply (sum_parallelograms_area d e a b f c DE AB AD BE)
  euclid_apply (sum_parallelograms_area d a f c h g AD CF DE AB)
  euclid_assert Triangle.area △ d:a:b + Triangle.area △ d:e:b = |(a─b)| * |(a─b)|
  euclid_assert Triangle.area △ d:a:b + Triangle.area △ d:e:b =
    (Triangle.area △ h:a:c + Triangle.area △ h:g:c) + (Triangle.area △ g:c:b + Triangle.area △ g:k:b) +
    (Triangle.area △ k:e:f + Triangle.area △ k:f:g) + (Triangle.area △ d:h:g + Triangle.area △ d:f:g)
  euclid_assert |(b─c)| * |(b─c)| = |(c─b)| * |(c─b)|
  euclid_assert |(c─a)| * |(c─a)| = |(a─c)| * |(a─c)|
  euclid_finish

end Elements.Book2
