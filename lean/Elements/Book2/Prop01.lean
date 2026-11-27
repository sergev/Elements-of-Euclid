import SystemE
import Elements.Book1.Prop29
import Elements.Book1.Prop30
import Elements.Book1.Prop31
import Elements.Book1.Prop34
import Elements.Book2.Lemmas

namespace Elements.Book2

open Elements.Book1

theorem proposition_1 : ∀ (a₁ a₂ b c d e : Point),
  a₁ ≠ a₂ ∧ between b d c ∧ between d e c →
  |(a₁─a₂)| * |(b─c)| = |(a₁─a₂)| * |(b─d)| + |(a₁─a₂)| * |(d─e)| + |(a₁─a₂)| * |(e─c)| :=
by
  euclid_intros
  euclid_apply (line_from_points b c) as BC
  euclid_apply (rectangle_on' b c a₁ a₂ BC) as (g, h, GH, BG, CH)
  euclid_apply (proposition_31 d b g BG) as DK
  euclid_apply (intersection_lines DK GH) as k
  euclid_apply (proposition_31 e b g BG) as EL
  euclid_apply (intersection_lines EL GH) as l
  -- Missed by Euclid: the parallels to BG are parallel to one another.
  euclid_apply (proposition_30 DK EL BG)
  euclid_apply (proposition_30 EL CH BG)
  euclid_apply (proposition_30 DK CH BG)
  euclid_apply (proposition_29_interior g k b d BG DK BC)
  euclid_apply (proposition_29_interior g l b e BG EL BC)
  euclid_apply (proposition_34' g k b d GH BC BG DK)
  euclid_apply (proposition_34' k l d e GH BC DK EL)
  euclid_apply (proposition_34' l h e c GH BC EL CH)
  euclid_apply (rectangle_area g k b d GH BC BG DK)
  euclid_apply (rectangle_area k l d e GH BC DK EL)
  euclid_apply (rectangle_area l h e c GH BC EL CH)
  euclid_apply (sum_parallelograms_area g h b c k d GH BC BG CH)
  euclid_apply (sum_parallelograms_area k h d c l e GH BC DK CH)
  euclid_assert Triangle.area △ g:b:c + Triangle.area △ g:h:c = |(a₁─a₂)| * |(b─c)|
  euclid_assert Triangle.area △ g:b:d + Triangle.area △ g:k:d = |(a₁─a₂)| * |(b─d)|
  euclid_assert Triangle.area △ k:d:e + Triangle.area △ k:l:e = |(a₁─a₂)| * |(d─e)|
  euclid_assert Triangle.area △ l:e:c + Triangle.area △ l:h:c = |(a₁─a₂)| * |(e─c)|
  euclid_assert Triangle.area △ g:b:c + Triangle.area △ g:h:c =
    (Triangle.area △ g:b:d + Triangle.area △ g:k:d) + (Triangle.area △ k:d:e + Triangle.area △ k:l:e) +
    (Triangle.area △ l:e:c + Triangle.area △ l:h:c)
  euclid_finish

end Elements.Book2
