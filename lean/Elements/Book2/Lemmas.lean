import SystemE
import Elements.Book1.Prop03
import Elements.Book1.Prop11
import Elements.Book1.Prop29
import Elements.Book1.Prop31
import Elements.Book1.Prop34

/-
Constructions Euclid repeats in Book 2. Def. 2.1 (the rectangle contained by two
straight-lines) is the product of their lengths, see `Elements/Book2.lean`; Def. 2.2
(the gnomon) is written out as a sum of triangle areas where it is used.
-/

namespace Elements.Book2

open Elements.Book1

/--
A rectangle on `ab` with height `a₁a₂`, on the side of `ab` away from `x`, and its area (Def. 2.1):
Prop. 1.46 with the side cut off equal to `a₁a₂` instead of `ab`.
Euclid draws it this way in Props. 2.1–2.3 ([Props. 1.11, 1.3, 1.31]).
-/
theorem rectangle_on : ∀ (a b x a₁ a₂ : Point) (AB : Line),
  ¬(x.onLine AB) ∧ distinctPointsOnLine a b AB ∧ a₁ ≠ a₂ →
  ∃ (d e : Point) (DE AD BE : Line), d.opposingSides x AB ∧ formParallelogram d e a b DE AB AD BE ∧
  |(d─e)| = |(a─b)| ∧ |(a─d)| = |(a₁─a₂)| ∧ |(b─e)| = |(a₁─a₂)| ∧
  (∠ b:a:d : ℝ) = ∟ ∧ (∠ a:d:e : ℝ) = ∟ ∧ (∠ a:b:e : ℝ) = ∟ ∧ (∠ b:e:d : ℝ) = ∟ ∧
  Triangle.area △ d:a:b + Triangle.area △ d:e:b = |(a─b)| * |(a₁─a₂)| :=
by
  euclid_intros
  euclid_apply (line_from_points a₁ a₂) as A₁₂
  euclid_apply (proposition_11_end_opposite a b x AB) as c'
  euclid_apply (line_from_points a c') as AC
  euclid_apply (extend_point_longer AC a c' (a₁─a₂)) as c
  euclid_apply (proposition_3 a c a₁ a₂ AC A₁₂) as d
  euclid_apply (proposition_31 d a b AB) as DE
  euclid_apply (proposition_31 b a d AC) as BE
  euclid_apply (intersection_lines DE BE) as e
  euclid_apply (proposition_34' d e a b DE AB AC BE)
  euclid_apply (proposition_29_interior e b d a DE AB AC)
  euclid_apply (proposition_34' d e a b DE AB AC BE)
  euclid_apply (rectangle_area d e a b DE AB AC BE)
  use d, e, DE, AC, BE
  euclid_finish

/--
`rectangle_on` without a side: Prop. 1.46 with the side cut off equal to `a₁a₂`.
-/
theorem rectangle_on' : ∀ (a b a₁ a₂ : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ a₁ ≠ a₂ →
  ∃ (d e : Point) (DE AD BE : Line), formParallelogram d e a b DE AB AD BE ∧
  |(d─e)| = |(a─b)| ∧ |(a─d)| = |(a₁─a₂)| ∧ |(b─e)| = |(a₁─a₂)| ∧
  (∠ b:a:d : ℝ) = ∟ ∧ (∠ a:d:e : ℝ) = ∟ ∧ (∠ a:b:e : ℝ) = ∟ ∧ (∠ b:e:d : ℝ) = ∟ ∧
  Triangle.area △ d:a:b + Triangle.area △ d:e:b = |(a─b)| * |(a₁─a₂)| :=
by
  euclid_intros
  euclid_apply (line_from_points a₁ a₂) as A₁₂
  euclid_apply (proposition_11_end a b AB) as c'
  euclid_apply (line_from_points a c') as AC
  euclid_apply (extend_point_longer AC a c' (a₁─a₂)) as c
  euclid_apply (proposition_3 a c a₁ a₂ AC A₁₂) as d
  euclid_apply (proposition_31 d a b AB) as DE
  euclid_apply (proposition_31 b a d AC) as BE
  euclid_apply (intersection_lines DE BE) as e
  euclid_apply (proposition_34' d e a b DE AB AC BE)
  euclid_apply (proposition_29_interior e b d a DE AB AC)
  euclid_apply (proposition_34' d e a b DE AB AC BE)
  euclid_apply (rectangle_area d e a b DE AB AC BE)
  use d, e, DE, AC, BE
  euclid_finish

/--
Parallels keep order: three parallel lines meeting one line at `x₁, x₂, x₃` in that order
meet any other line in the same order. Euclid reads this off his figures.
-/
theorem parallel_between : ∀ (x₁ x₂ x₃ y₁ y₂ y₃ : Point) (L₁ L₂ L₃ T : Line),
  x₁.onLine L₁ ∧ y₁.onLine L₁ ∧ x₂.onLine L₂ ∧ y₂.onLine L₂ ∧ x₃.onLine L₃ ∧ y₃.onLine L₃ ∧
  y₁.onLine T ∧ y₂.onLine T ∧ y₃.onLine T ∧ between x₁ x₂ x₃ ∧
  L₁ ≠ L₂ ∧ L₂ ≠ L₃ ∧ ¬(L₁.intersectsLine L₂) ∧ ¬(L₂.intersectsLine L₃) ∧ ¬(L₁.intersectsLine L₃) →
  between y₁ y₂ y₃ :=
by
  euclid_intros
  euclid_assert x₁.opposingSides x₃ L₂
  euclid_assert y₁.sameSide x₁ L₂
  euclid_assert y₃.sameSide x₃ L₂
  euclid_assert y₁.opposingSides y₃ L₂
  euclid_finish

end Elements.Book2
