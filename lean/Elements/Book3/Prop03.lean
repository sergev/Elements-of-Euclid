import SystemE
import Elements.Book1.Prop05
import Elements.Book1.Prop08
import Elements.Book1.Prop10
import Elements.Book1.Prop17
import Elements.Book1.Prop26

namespace Elements.Book3

/--
A straight line through the center `E` cutting a chord `AB`, not through the center,
in half at `F` cuts it at right angles.
-/
theorem proposition_3 : ∀ (a b e f : Point) (AB : Line) (α : Circle),
  distinctPointsOnLine a b AB ∧ a.onCircle α ∧ b.onCircle α ∧ e.isCentre α ∧
  ¬(e.onLine AB) ∧ between a f b ∧ |(a─f)| = |(f─b)| → ∠ a:f:e = ∟ :=
by
  euclid_intros
  euclid_apply (line_from_points e a) as EA
  euclid_apply (line_from_points e b) as EB
  euclid_apply (line_from_points e f) as EF
  euclid_apply (point_on_circle_onlyif e a b α)
  -- AF = FB, FE common, EA = EB: the angles at F are equal [Prop. 1.8], so right
  euclid_apply (Elements.Book1.proposition_8 f a e f b e AB EA EF AB EB EF)
  euclid_apply (perpendicular_if a b f e AB)
  euclid_finish

/-- Conversely, if it cuts `AB` at right angles, it cuts it in half. -/
theorem proposition_3' : ∀ (a b e f : Point) (AB : Line) (α : Circle),
  distinctPointsOnLine a b AB ∧ a.onCircle α ∧ b.onCircle α ∧ e.isCentre α ∧
  ¬(e.onLine AB) ∧ between a f b ∧ ∠ a:f:e = ∟ → |(a─f)| = |(f─b)| :=
by
  euclid_intros
  euclid_apply (line_from_points e a) as EA
  euclid_apply (line_from_points e b) as EB
  euclid_apply (line_from_points e f) as EF
  euclid_apply (point_on_circle_onlyif e a b α)
  -- EA = EB, so the angles EAF, EBF are equal [Prop. 1.5]
  euclid_apply (Elements.Book1.proposition_5' e a b EA AB EB)
  euclid_apply (equal_angles a e e b f EA AB)
  euclid_apply (equal_angles b e e a f EB AB)
  -- the angles at F are right
  euclid_apply (perpendicular_onlyif a b f e AB)
  -- two angles and the side EA = EB [Prop. 1.26]
  euclid_apply (Elements.Book1.proposition_26 e a f e b f EA AB EF EB AB EF)
  euclid_finish

/--
The perpendicular `EF` from the center to a chord `AB` falls at its midpoint: there `AB`
is cut in half [Prop. 1.10], at right angles (3.3), and two perpendiculars from `E`
would make a triangle with two right angles [Prop. 1.17].
-/
theorem proposition_3_foot : ∀ (a b e f : Point) (AB : Line) (α : Circle),
  distinctPointsOnLine a b AB ∧ a.onCircle α ∧ b.onCircle α ∧ e.isCentre α ∧
  ¬(e.onLine AB) ∧ f.onLine AB ∧ f ≠ a ∧ ∠ a:f:e = ∟ →
  between a f b ∧ |(a─f)| = |(f─b)| :=
by
  euclid_intros
  euclid_apply (Elements.Book1.proposition_10 a b AB) as m
  euclid_apply (proposition_3 a b e m AB α)
  by_cases (f = m)
  · euclid_finish
  · euclid_apply (line_from_points e m) as EM
    euclid_apply (line_from_points e f) as EF
    euclid_apply (right_angle_on_lines a m e f e AB EM)
    euclid_apply (right_angle_on_lines a f e m e AB EF)
    euclid_apply (Elements.Book1.proposition_17 e m f EM AB EF)
    exfalso
    euclid_finish

end Elements.Book3
