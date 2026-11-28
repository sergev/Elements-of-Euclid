import SystemE
import Elements.Book1.Prop05
import Elements.Book1.Prop06
import Elements.Book1.Prop29
import Elements.Book1.Prop30
import Elements.Book1.Prop31
import Elements.Book1.Prop34
import Elements.Book1.Prop36
import Elements.Book1.Prop43
import Elements.Book1.Prop46
import Elements.Book2.Lemmas

namespace Elements.Book2

open Elements.Book1

set_option maxHeartbeats 2000000 in
theorem proposition_5 : ∀ (a b c d : Point),
  between a c b ∧ between c d b ∧ |(a─c)| = |(c─b)| →
  |(a─d)| * |(d─b)| + |(c─d)| * |(c─d)| = |(c─b)| * |(c─b)| :=
by
  euclid_intros
  euclid_apply (line_from_points a b) as AB
  euclid_apply (proposition_46 c b AB) as (e, f, EF, CE, BF)
  euclid_apply (line_from_points b e) as BE
  euclid_apply (proposition_31 d c e CE) as DG
  euclid_apply (intersection_lines DG BE) as h
  euclid_apply (intersection_lines DG EF) as g
  euclid_apply (proposition_31 h c b AB) as KM
  euclid_apply (intersection_lines KM CE) as l
  euclid_apply (intersection_lines KM BF) as m
  euclid_apply (proposition_31 a c e CE) as AK
  euclid_apply (intersection_lines AK KM) as k
  -- Missed by Euclid.
  euclid_apply (proposition_30 DG BF CE)
  euclid_apply (proposition_30 KM EF AB)
  euclid_apply (proposition_30 AK DG CE)
  euclid_apply (proposition_30 AK BF CE)
  -- the sides of the figures
  euclid_apply (proposition_34' l h c d KM AB CE DG)
  euclid_apply (proposition_34' h m d b KM AB DG BF)
  euclid_apply (proposition_34' e g l h EF KM CE DG)
  euclid_apply (proposition_34' k l a c KM AB AK CE)
  euclid_apply (proposition_34' k h a d KM AB AK DG)
  -- DH = DB
  euclid_apply (proposition_29_exterior d c b h e DG CE BE)
  euclid_apply (proposition_5' c e b CE BE AB)
  euclid_apply (proposition_6 d h b DG BE AB)
  -- Missed by Euclid: LG is the square on CD.
  euclid_apply (proposition_29_exterior l c e h b KM AB BE)
  euclid_apply (proposition_6 l e h CE BE KM)
  -- the right angles
  euclid_apply (proposition_29_interior e k c a CE AK AB)
  euclid_apply (proposition_29_interior e h c d CE DG AB)
  euclid_apply (proposition_29_exterior h b e l c KM AB CE)
  euclid_apply (rectangle_area l h c d KM AB CE DG)
  euclid_apply (right_angle_on_lines h d c h b DG AB)
  euclid_apply (rectangle_area h m d b KM AB DG BF)
  euclid_apply (rectangle_area e g l h EF KM CE DG)
  euclid_apply (rectangle_area k h a d KM AB AK DG)
  euclid_apply (rectangle_area e f c b EF AB CE BF)
  -- the complements CH, HF are equal; CM = AL
  euclid_apply (proposition_43 b f e c m l g d h AB EF BF CE BE KM DG)
  euclid_apply (proposition_36' k a c l l c b m KM AB AK CE CE BF)
  -- how the figures make up one another
  euclid_apply (parallel_between c d b e g f CE DG BF EF)
  euclid_apply (sum_parallelograms_area e f c b g d EF AB CE BF)
  euclid_apply (sum_parallelograms_area e c g d l h CE DG EF AB)
  euclid_apply (parallel_between c d b e h b CE DG BF BE)
  euclid_apply (parallel_between e h b g h d EF KM AB DG)
  euclid_apply (parallel_between e h b f m b EF KM AB BF)
  euclid_apply (sum_parallelograms_area g d f b h m DG BF EF AB)
  euclid_apply (sum_parallelograms_area k h a d l c KM AB AK DG)
  euclid_apply (sum_parallelograms_area l m c b h d KM AB CE BF)
  euclid_assert Triangle.area △ l:c:d + Triangle.area △ l:h:d = Triangle.area △ m:f:g + Triangle.area △ m:g:h
  euclid_assert Triangle.area △ k:a:c + Triangle.area △ k:l:c =
    (Triangle.area △ l:c:d + Triangle.area △ l:h:d) + (Triangle.area △ h:d:b + Triangle.area △ h:m:b)
  euclid_assert Triangle.area △ k:a:d + Triangle.area △ k:h:d =
    (Triangle.area △ l:c:d + Triangle.area △ l:h:d) + (Triangle.area △ h:d:b + Triangle.area △ h:m:b) +
    (Triangle.area △ m:f:g + Triangle.area △ m:g:h)
  euclid_assert Triangle.area △ k:a:d + Triangle.area △ k:h:d = |(a─d)| * |(d─b)|
  euclid_assert Triangle.area △ e:l:h + Triangle.area △ e:g:h = |(c─d)| * |(c─d)|
  euclid_assert Triangle.area △ e:c:b + Triangle.area △ e:f:b =
    (Triangle.area △ l:c:d + Triangle.area △ l:h:d) + (Triangle.area △ h:d:b + Triangle.area △ h:m:b) +
    (Triangle.area △ m:f:g + Triangle.area △ m:g:h) + (Triangle.area △ e:l:h + Triangle.area △ e:g:h)
  euclid_assert Triangle.area △ e:c:b + Triangle.area △ e:f:b = |(c─b)| * |(c─b)|
  euclid_finish

end Elements.Book2
