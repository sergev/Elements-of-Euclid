import SystemE
import Elements.Book1.Prop03
import Elements.Book1.Prop10
import Elements.Book1.Prop11
import Elements.Book1.Prop34
import Elements.Book1.Prop45
import Elements.Book1.Prop47
import Elements.Book2.Prop05

namespace Elements.Book2

open Elements.Book1

/--
The semicircle of Prop. 2.14: for a right angle `BED` with `BE` greater than `ED`,
the square on `EH` equals the rectangle on `BE`, `ED`.
-/
theorem proposition_14_lemma : ∀ (b e d : Point) (BE ED : Line),
  distinctPointsOnLine b e BE ∧ distinctPointsOnLine e d ED ∧ (∠ b:e:d : ℝ) = ∟ ∧ |(e─b)| > |(e─d)| →
  ∃ h : Point, |(e─h)| * |(e─h)| = |(e─b)| * |(e─d)| :=
by
  euclid_intros
  euclid_apply (extend_point_longer BE b e (e─d)) as x
  euclid_apply (Elements.Book1.proposition_3 e x e d BE ED) as f
  euclid_apply (Elements.Book1.proposition_10 b f BE) as g
  -- Missed by Euclid: E falls between G and F, since BE is greater than EF.
  euclid_assert between g e f
  euclid_apply (circle_from_points g b) as BHF
  euclid_apply (intersection_circle_line_extending_points BHF ED e d) as h
  euclid_apply (line_from_points g h) as GH
  -- BF is cut equally at G and unequally at E [Prop. 2.5]
  euclid_apply (Elements.Book2.proposition_5 b f g e)
  -- GH = GF, and the angle at E is right [Prop. 1.47]
  have := right_angle_pos
  euclid_apply (not_on_line_of_angle b e d BE ED)
  euclid_apply (right_angle_on_lines b e d g h BE ED)
  euclid_apply (proposition_47 e h g ED GH BE)
  use h
  euclid_finish

theorem proposition_14 : ∀ (a b c d : Point) (AB BC CD AD DB : Line),
  formTriangle a b d AB DB AD ∧ formTriangle b c d BC CD DB ∧ a.opposingSides c DB →
  ∃ (e h : Point), |(e─h)| * |(e─h)| = Triangle.area △ a:b:d + Triangle.area △ d:b:c :=
by
  euclid_intros
  -- the right-angled parallelogram equal to the figure [Prop. 1.45]
  euclid_apply (proposition_11_end d b DB) as x
  euclid_apply (line_from_points x d) as XD
  euclid_apply (proposition_45 a b c d x d b AB BC CD AD DB XD DB) as (f, l, k, m, FL, KM, FK, LM)
  euclid_apply (proposition_34' f l k m FL KM FK LM)
  euclid_apply (rectangle_area f l k m FL KM FK LM)
  euclid_assert Triangle.area △ a:b:d + Triangle.area △ d:b:c = |(k─f)| * |(k─m)|
  by_cases hq : |(k─f)| = |(k─m)|
  · -- it is a square already
    use k, f
    euclid_finish
  · rcases lt_or_gt_of_ne hq with hlt | hgt
    · obtain ⟨h, hh⟩ := proposition_14_lemma m k f KM FK (by euclid_finish)
      use k, h
      euclid_finish
    · obtain ⟨h, hh⟩ := proposition_14_lemma f k m FK KM (by euclid_finish)
      use k, h
      euclid_finish

end Elements.Book2
