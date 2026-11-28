import SystemE
import Elements.Book1.Prop12
import Elements.Book1.Prop47
import Elements.Book2.Prop05
import Elements.Book3.Prop03

namespace Elements.Book3

/--
Prop. 2.5 for a point `E` anywhere on `AC`, cut in half at `G`: the rectangle `AE`, `EC`
and the square on `GE` make the square on `GC`.
-/
theorem proposition_35_halves : ∀ (a c e g : Point),
  between a g c ∧ |(a─g)| = |(g─c)| ∧ between a e c →
  |(a─e)| * |(e─c)| + |(g─e)| * |(g─e)| = |(g─c)| * |(g─c)| :=
by
  euclid_intros
  by_cases (e = g)
  · have h0 : |(g─g)| * |(g─g)| = 0 := by rw [zero_segment_onlyif g g rfl, mul_zero]
    euclid_assert |(a─g)| * |(g─c)| = |(g─c)| * |(g─c)|
    euclid_finish
  · by_cases (between g e c)
    · euclid_apply (Elements.Book2.proposition_5 a c g e)
      euclid_finish
    · euclid_apply (line_from_points a c) as AC
      euclid_apply (between_points a e g AC)
      have : between a e g := by
        rcases ‹_ ∨ _ ∨ _› with _ | _ | _
        · assumption
        · exfalso
          euclid_finish
        · exfalso
          euclid_apply (between_trans_in' a e c g)
          euclid_finish
      euclid_apply (Elements.Book2.proposition_5 c a g e)
      euclid_assert |(c─e)| * |(e─a)| = |(a─e)| * |(e─c)|
      euclid_finish

/--
Euclid's argument in Prop. 3.35, for one chord `AC` through `E`, with the center `F`: the
rectangle `AE`, `EC` and the square on `FE` make the square on `FC` [Props. 3.3, 2.5,
1.47].
-/
theorem proposition_35_lemma : ∀ (a c e f : Point) (AC : Line) (α : Circle),
  a.onCircle α ∧ c.onCircle α ∧ distinctPointsOnLine a c AC ∧ between a e c ∧
  f.isCentre α → |(a─e)| * |(e─c)| + |(f─e)| * |(f─e)| = |(f─c)| * |(f─c)| :=
by
  euclid_intros
  by_cases (f.onLine AC)
  · -- AC is through the center, cut in half at F
    euclid_apply (circle_line_intersections f a c AC α)
    euclid_apply (point_on_circle_onlyif f a c α)
    euclid_apply (proposition_35_halves a c e f)
    euclid_finish
  · -- FG perpendicular to AC [Prop. 1.12] cuts it in half [Prop. 3.3]
    euclid_apply (Elements.Book1.proposition_12 a c f AC) as g
    euclid_apply (line_from_points g f) as GF
    have : between a g c ∧ |(a─g)| = |(g─c)| ∧ ∠ a:g:f = ∟ := by
      rcases ‹_ ∨ _› with ⟨_, _⟩ | ⟨_, _⟩
      · euclid_apply (proposition_3_foot a c f g AC α)
        euclid_finish
      · euclid_apply (proposition_3_foot c a f g AC α)
        euclid_apply (right_angle_on_lines c g f a f AC GF)
        euclid_finish
    -- the rectangle AE, EC and the square on EG make the square on GC [Prop. 2.5]
    euclid_apply (proposition_35_halves a c e g)
    -- add the square on GF: those on GE, GF make that on FE, and those on CG, GF that on
    -- FC [Prop. 1.47]
    euclid_apply (line_from_points c f) as CF
    euclid_apply (right_angle_on_lines a g f c f AC GF)
    euclid_apply (Elements.Book1.proposition_47 g c f AC CF GF)
    euclid_assert |(c─f)| * |(c─f)| = |(f─c)| * |(f─c)|
    euclid_assert |(c─g)| * |(c─g)| = |(g─c)| * |(g─c)|
    by_cases (e = g)
    · have h0 : |(g─g)| * |(g─g)| = 0 := by rw [zero_segment_onlyif g g rfl, mul_zero]
      euclid_assert |(f─g)| * |(f─g)| = |(g─f)| * |(g─f)|
      euclid_finish
    · euclid_apply (line_from_points e f) as EF
      euclid_apply (right_angle_on_lines a g f e f AC GF)
      euclid_apply (Elements.Book1.proposition_47 g e f AC EF GF)
      euclid_assert |(e─f)| * |(e─f)| = |(f─e)| * |(f─e)|
      euclid_assert |(e─g)| * |(e─g)| = |(g─e)| * |(g─e)|
      euclid_finish

/--
Chords `AC`, `BD` cutting at `E`: the rectangle `AE`, `EC` is equal to the rectangle
`DE`, `EB`.
-/
theorem proposition_35 : ∀ (a b c d e f : Point) (AC BD : Line) (α : Circle),
  a.onCircle α ∧ b.onCircle α ∧ c.onCircle α ∧ d.onCircle α ∧
  distinctPointsOnLine a c AC ∧ distinctPointsOnLine b d BD ∧ between a e c ∧
  between b e d ∧ f.isCentre α → |(a─e)| * |(e─c)| = |(d─e)| * |(e─b)| :=
by
  euclid_intros
  -- with the center F (Euclid: if AC, BD are through the center, it is clear; otherwise
  -- this): the rectangle AE, EC and the square on FE make the square on FC = FB, and so
  -- do the rectangle DE, EB and the square on FE
  euclid_apply (proposition_35_lemma a c e f AC α)
  euclid_apply (proposition_35_lemma d b e f BD α)
  euclid_apply (point_on_circle_onlyif f c b α)
  euclid_assert |(f─c)| * |(f─c)| = |(f─b)| * |(f─b)|
  euclid_finish

end Elements.Book3
