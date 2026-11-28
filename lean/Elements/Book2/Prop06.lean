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
theorem proposition_6 : ∀ (a b c d : Point),
  between a c b ∧ between c b d ∧ |(a─c)| = |(c─b)| →
  |(a─d)| * |(d─b)| + |(c─b)| * |(c─b)| = |(c─d)| * |(c─d)| :=
by
  euclid_intros
  euclid_apply (line_from_points a d) as AB
  euclid_apply (proposition_46 c d AB) as (e, f, EF, CE, DF)
  euclid_apply (line_from_points d e) as DE
  euclid_apply (proposition_31 b c e CE) as BG
  euclid_apply (intersection_lines BG DE) as h
  euclid_apply (intersection_lines BG EF) as g
  euclid_apply (proposition_31 h c d AB) as KM
  euclid_apply (intersection_lines KM CE) as l
  euclid_apply (intersection_lines KM DF) as m
  euclid_apply (proposition_31 a c e CE) as AK
  euclid_apply (intersection_lines AK KM) as k
  -- Missed by Euclid.
  euclid_apply (proposition_30 BG DF CE)
  euclid_apply (proposition_30 KM EF AB)
  euclid_apply (proposition_30 AK BG CE)
  euclid_apply (proposition_30 AK DF CE)
  -- the sides of the figures
  euclid_apply (proposition_34' l h c b KM AB CE BG)
  euclid_apply (proposition_34' h m b d KM AB BG DF)
  euclid_apply (proposition_34' e g l h EF KM CE BG)
  euclid_apply (proposition_34' k l a c KM AB AK CE)
  euclid_apply (proposition_34' k m a d KM AB AK DF)
  -- DM = DB
  euclid_apply (proposition_29_exterior b c d h e BG CE DE)
  euclid_apply (proposition_5' c e d CE DE AB)
  euclid_apply (Elements.Book1.proposition_6 b h d BG DE AB)
  -- Missed by Euclid: LG is the square on CB.
  euclid_apply (proposition_29_exterior l c e h d KM AB DE)
  euclid_apply (Elements.Book1.proposition_6 l e h CE DE KM)
  -- the right angles
  euclid_apply (proposition_29_interior e k c a CE AK AB)
  euclid_apply (proposition_29_interior e h c b CE BG AB)
  euclid_apply (proposition_29_exterior h d e l c KM AB CE)
  euclid_apply (rectangle_area l h c b KM AB CE BG)
  euclid_apply (right_angle_on_lines h b c h d BG AB)
  euclid_apply (rectangle_area h m b d KM AB BG DF)
  euclid_apply (rectangle_area e g l h EF KM CE BG)
  euclid_apply (rectangle_area k m a d KM AB AK DF)
  euclid_apply (rectangle_area e f c d EF AB CE DF)
  -- AL = CH, and CH = HF
  euclid_apply (proposition_36' k a c l l c b h KM AB AK CE CE BG)
  euclid_apply (proposition_43 d f e c m l g b h AB EF DF CE DE KM BG)
  -- how the figures make up one another
  euclid_apply (parallel_between c b d e g f CE BG DF EF)
  euclid_apply (sum_parallelograms_area e f c d g b EF AB CE DF)
  euclid_apply (sum_parallelograms_area e c g b l h CE BG EF AB)
  euclid_apply (parallel_between c b d e h d CE BG DF DE)
  euclid_apply (parallel_between e h d g h b EF KM AB BG)
  euclid_apply (parallel_between e h d f m d EF KM AB DF)
  euclid_apply (sum_parallelograms_area g b f d h m BG DF EF AB)
  euclid_apply (sum_parallelograms_area k m a d l c KM AB AK DF)
  euclid_apply (sum_parallelograms_area l m c d h b KM AB CE DF)
  euclid_assert Triangle.area △ k:a:c + Triangle.area △ k:l:c = Triangle.area △ l:c:b + Triangle.area △ l:h:b
  euclid_assert Triangle.area △ l:c:b + Triangle.area △ l:h:b = Triangle.area △ m:f:g + Triangle.area △ m:g:h
  euclid_assert Triangle.area △ k:a:d + Triangle.area △ k:m:d =
    (Triangle.area △ l:c:b + Triangle.area △ l:h:b) + (Triangle.area △ h:b:d + Triangle.area △ h:m:d) +
    (Triangle.area △ m:f:g + Triangle.area △ m:g:h)
  euclid_assert Triangle.area △ k:a:d + Triangle.area △ k:m:d = |(a─d)| * |(d─b)|
  euclid_assert Triangle.area △ e:l:h + Triangle.area △ e:g:h = |(c─b)| * |(c─b)|
  euclid_assert Triangle.area △ e:c:d + Triangle.area △ e:f:d =
    (Triangle.area △ l:c:b + Triangle.area △ l:h:b) + (Triangle.area △ h:b:d + Triangle.area △ h:m:d) +
    (Triangle.area △ m:f:g + Triangle.area △ m:g:h) + (Triangle.area △ e:l:h + Triangle.area △ e:g:h)
  euclid_assert Triangle.area △ e:c:d + Triangle.area △ e:f:d = |(c─d)| * |(c─d)|
  euclid_finish

end Elements.Book2
