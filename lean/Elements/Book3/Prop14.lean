import SystemE
import Elements.Book1.Prop47
import Elements.Book3.Lemmas
import Elements.Book3.Prop03

namespace Elements.Book3

/-
Prop. 3.14. Chords `AB` and `CD` of a circle with center `E`, not through the center,
and the perpendiculars `EF`, `EG` on them: their distances from the center (Def. 3.4).
-/

/-- Equal chords are equally far from the center. -/
theorem proposition_14 : ∀ (a b c d e f g : Point) (AB CD : Line) (α : Circle),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧
  a.onCircle α ∧ b.onCircle α ∧ c.onCircle α ∧ d.onCircle α ∧ e.isCentre α ∧
  ¬(e.onLine AB) ∧ ¬(e.onLine CD) ∧ f.onLine AB ∧ f ≠ a ∧ ∠ a:f:e = ∟ ∧
  g.onLine CD ∧ g ≠ c ∧ ∠ c:g:e = ∟ ∧ |(a─b)| = |(c─d)| → |(e─f)| = |(e─g)| :=
by
  euclid_intros
  -- EF cuts AB in half, and EG cuts CD in half [Prop. 3.3]; so AF = CG
  euclid_apply (proposition_3_foot a b e f AB α)
  euclid_apply (proposition_3_foot c d e g CD α)
  euclid_apply (between_if a f b)
  euclid_apply (between_if c g d)
  -- the squares on AF, FE make the square on AE = EC, as those on CG, GE [Prop. 1.47]
  euclid_apply (line_from_points a e) as AE
  euclid_apply (line_from_points c e) as CE
  euclid_apply (line_from_points f e) as FE
  euclid_apply (line_from_points g e) as GE
  euclid_apply (Elements.Book1.proposition_47 f a e AB AE FE)
  euclid_apply (Elements.Book1.proposition_47 g c e CD CE GE)
  euclid_apply (point_on_circle_onlyif e a c α)
  euclid_assert |(a─e)| = |(c─e)|
  euclid_assert |(a─f)| = |(c─g)|
  -- take away the equal squares on AF, CG: the squares on FE, EG are equal
  euclid_assert |(f─e)| * |(f─e)| = |(g─e)| * |(g─e)|
  euclid_apply (length_eq_of_square_eq f e g e)
  euclid_finish

/-- Chords equally far from the center are equal. -/
theorem proposition_14' : ∀ (a b c d e f g : Point) (AB CD : Line) (α : Circle),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧
  a.onCircle α ∧ b.onCircle α ∧ c.onCircle α ∧ d.onCircle α ∧ e.isCentre α ∧
  ¬(e.onLine AB) ∧ ¬(e.onLine CD) ∧ f.onLine AB ∧ f ≠ a ∧ ∠ a:f:e = ∟ ∧
  g.onLine CD ∧ g ≠ c ∧ ∠ c:g:e = ∟ ∧ |(e─f)| = |(e─g)| → |(a─b)| = |(c─d)| :=
by
  euclid_intros
  -- AB is double AF, and CD double CG [Prop. 3.3]
  euclid_apply (proposition_3_foot a b e f AB α)
  euclid_apply (proposition_3_foot c d e g CD α)
  euclid_apply (between_if a f b)
  euclid_apply (between_if c g d)
  -- the squares on EF, FA make the square on AE = CE, as those on EG, GC [Prop. 1.47]
  euclid_apply (line_from_points a e) as AE
  euclid_apply (line_from_points c e) as CE
  euclid_apply (line_from_points f e) as FE
  euclid_apply (line_from_points g e) as GE
  euclid_apply (Elements.Book1.proposition_47 f a e AB AE FE)
  euclid_apply (Elements.Book1.proposition_47 g c e CD CE GE)
  euclid_apply (point_on_circle_onlyif e a c α)
  euclid_assert |(a─e)| = |(c─e)|
  euclid_assert |(f─e)| = |(g─e)|
  -- take away the equal squares on EF, EG: the squares on AF, CG are equal
  euclid_assert |(a─f)| * |(a─f)| = |(c─g)| * |(c─g)|
  euclid_apply (length_eq_of_square_eq a f c g)
  euclid_finish

end Elements.Book3
