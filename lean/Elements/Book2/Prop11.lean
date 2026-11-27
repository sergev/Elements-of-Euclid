import SystemE
import Elements.Book1.Prop03
import Elements.Book1.Prop10
import Elements.Book1.Prop30
import Elements.Book1.Prop34
import Elements.Book1.Prop46
import Elements.Book1.Prop47
import Elements.Book2.Prop06

namespace Elements.Book2

open Elements.Book1

theorem proposition_11 : ∀ (a b : Point) (AB : Line),
  distinctPointsOnLine a b AB →
  ∃ h : Point, between a h b ∧ |(a─b)| * |(b─h)| = |(a─h)| * |(a─h)| :=
by
  euclid_intros
  euclid_apply (proposition_46 a b AB) as (c, d, CD, AC, BD)
  euclid_apply (Elements.Book1.proposition_10 a c AC) as e
  euclid_apply (line_from_points b e) as BE
  euclid_apply (extend_point_longer AC e a (e─b)) as x
  euclid_apply (Elements.Book1.proposition_3 e x e b AC BE) as f
  -- Missed by Euclid: F falls beyond A, since EB is greater than EA.
  euclid_apply (proposition_47 a b e AB BE AC)
  euclid_assert between e a f
  euclid_apply (exists_point_opposite AC b) as z
  euclid_apply (proposition_46' f a z AC) as (g, h, GH, FG, AH)
  -- Missed by Euclid: H falls on AB.
  euclid_assert h.onLine AB
  euclid_assert AH = AB
  euclid_apply (proposition_30 GH BD AC)
  euclid_apply (intersection_lines GH CD) as k
  euclid_apply (proposition_30 FG CD AB)
  -- CF, FA with the square on AE make the square on EF [Prop. 2.6]
  euclid_apply (Elements.Book2.proposition_6 c a e f)
  set_option systemE.simpAll false in
    euclid_assert |(e─f)| * |(e─f)| = |(e─b)| * |(e─b)|
  set_option systemE.simpAll false in
    euclid_assert |(b─e)| * |(b─e)| = |(e─b)| * |(e─b)|
  set_option systemE.simpAll false in
    euclid_assert |(b─a)| * |(b─a)| = |(a─b)| * |(a─b)|
  set_option systemE.simpAll false in
    euclid_assert |(a─e)| * |(a─e)| = |(e─a)| * |(e─a)|
  set_option systemE.simpAll false in
    euclid_assert |(e─b)| * |(e─b)| = |(a─b)| * |(a─b)| + |(e─a)| * |(e─a)|
  set_option systemE.simpAll false in
    euclid_assert |(c─f)| * |(f─a)| = |(a─b)| * |(a─b)|
  -- Missed by Euclid: H falls between A and B, since AH = FA is less than AB.
  euclid_assert |(c─f)| = |(a─b)| + |(f─a)|
  euclid_assert |(f─a)| < |(a─b)|
  euclid_assert |(a─h)| < |(a─b)| ∧ h.sameSide b AC
  euclid_assert h ≠ a ∧ h ≠ b
  euclid_assert ¬(between a b h)
  euclid_assert ¬(between h a b)
  euclid_apply (between_points a h b AB)
  euclid_assert between a h b
  -- FK is the rectangle on CF, FA; AD the square on AB
  euclid_apply (proposition_34' f g c k FG CD AC GH)
  euclid_apply (rectangle_area f g c k FG CD AC GH)
  euclid_apply (rectangle_area a b c d AB CD AC BD)
  euclid_assert |(f─g)| = |(f─a)| ∧ |(f─c)| = |(c─f)|
  set_option systemE.simpAll false in
    euclid_assert |(f─g)| * |(f─c)| = |(c─f)| * |(f─a)|
  set_option systemE.simpAll false in
    euclid_assert Triangle.area △ f:c:k + Triangle.area △ f:g:k = |(c─f)| * |(f─a)|
  -- take away AK: FH = HD
  euclid_apply (sum_parallelograms_area f c g k a h AC GH FG CD)
  euclid_apply (sum_parallelograms_area a b c d h k AB CD AC BD)
  euclid_apply (proposition_34' h b k d AB CD GH BD)
  euclid_apply (rectangle_area h b k d AB CD GH BD)
  euclid_apply (rectangle_area f g a h FG AB AC GH)
  set_option systemE.simpAll false in
    euclid_assert Triangle.area △ f:a:h + Triangle.area △ f:g:h = Triangle.area △ h:k:d + Triangle.area △ h:b:d
  -- HD is the rectangle on AB, BH; FH the square on AH
  euclid_assert |(h─k)| = |(a─b)| ∧ |(h─b)| = |(b─h)| ∧ |(a─h)| = |(f─a)| ∧ |(f─g)| = |(f─a)|
  set_option systemE.simpAll false in
    euclid_assert Triangle.area △ h:k:d + Triangle.area △ h:b:d = |(a─b)| * |(b─h)|
  set_option systemE.simpAll false in
    euclid_assert Triangle.area △ f:a:h + Triangle.area △ f:g:h = |(f─g)| * |(f─a)|
  set_option systemE.simpAll false in
    euclid_assert |(f─g)| * |(f─a)| = |(a─h)| * |(a─h)|
  set_option systemE.simpAll false in
    euclid_assert Triangle.area △ f:a:h + Triangle.area △ f:g:h = |(a─h)| * |(a─h)|
  use h
  set_option systemE.simpAll false in euclid_finish

end Elements.Book2
