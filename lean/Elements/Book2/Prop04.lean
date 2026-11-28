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

/--
The figure of Props. 2.4 and 2.7: the square `ADEB` on `AB`, its diagonal `BD`, the parallel
`CF` to `AD` meeting `BD` at `G`, and `HK` through `G` parallel to `AB`.
-/
theorem proposition_4_figure : ∀ (a b c : Point),
  between a c b →
  ∃ (d e f g h k : Point),
  ▱ d:e:a:b = |(a─b)| * |(a─b)| ∧ ▱ d:f:h:g = |(a─c)| * |(a─c)| ∧ ▱ g:k:c:b = |(c─b)| * |(c─b)| ∧
  ▱ h:g:a:c = |(a─c)| * |(c─b)| ∧ ▱ k:g:e:f = |(a─c)| * |(c─b)| ∧ ▱ h:k:a:b = |(a─b)| * |(b─c)| ∧
  ▱ d:e:a:b = ▱ d:f:h:g + ▱ g:k:c:b + ▱ h:g:a:c + ▱ k:g:e:f ∧
  ▱ h:k:a:b = ▱ h:g:a:c + ▱ g:k:c:b ∧ ▱ f:e:c:b = ▱ g:k:c:b + ▱ k:g:e:f :=
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
  euclid_apply (right_angle_on_lines g c a g b CF AB)
  euclid_apply (rectangle_area g k c b HK AB CF BE)
  euclid_assert ▱ g:k:c:b = |(c─b)| * |(c─b)|
  -- HF is a square on AC
  euclid_apply (proposition_34' h g a c HK AB AD CF)
  euclid_apply (proposition_34' d f h g DE HK AD CF)
  euclid_apply (proposition_29_interior b g a h AB HK AD)
  euclid_apply (right_angle_on_lines g h a g d HK AD)
  euclid_assert |(d─h)| = |(a─c)|
  euclid_assert |(d─f)| = |(a─c)|
  euclid_apply (rectangle_area d f h g DE HK AD CF)
  euclid_assert ▱ d:f:h:g = |(a─c)| * |(a─c)|
  -- AG = GE, and AG is the rectangle on AC, CB
  euclid_apply (rectangle_area h g a c HK AB AD CF)
  euclid_assert ▱ h:g:a:c = |(a─c)| * |(c─b)|
  euclid_apply (proposition_43 b e d a k h f c g AB DE BE AD BD HK CF)
  euclid_assert ▱ k:g:e:f = |(a─c)| * |(c─b)|
  -- the four make up the square on AB
  euclid_apply (rectangle_area d e a b DE AB AD BE)
  euclid_apply (sum_parallelograms_area d e a b f c DE AB AD BE)
  euclid_apply (sum_parallelograms_area d a f c h g AD CF DE AB)
  euclid_apply (sum_parallelograms_area f c e b g k CF BE DE AB)
  euclid_assert ▱ d:e:a:b = |(a─b)| * |(a─b)|
  -- AK is AG and CK, CE is CK and GE; AK is the rectangle on AB, BC
  euclid_apply (sum_parallelograms_area h k a b g c HK AB AD BE)
  euclid_apply (sum_parallelograms_area f c e b g k CF BE DE AB)
  euclid_apply (proposition_34' h k a b HK AB AD BE)
  euclid_apply (rectangle_area h k a b HK AB AD BE)
  euclid_assert ▱ h:k:a:b = |(a─b)| * |(b─c)|
  use d, e, f, g, h, k
  euclid_finish

theorem proposition_4 : ∀ (a b c : Point),
  between a c b →
  |(a─b)| * |(a─b)| = |(a─c)| * |(a─c)| + |(c─b)| * |(c─b)| + 2 * (|(a─c)| * |(c─b)|) :=
by
  euclid_intros
  euclid_apply (proposition_4_figure a b c) as (d, e, f, g, h, k)
  -- the square on AB is HF, CK, and AG, GE, each the rectangle on AC, CB
  euclid_finish

end Elements.Book2
