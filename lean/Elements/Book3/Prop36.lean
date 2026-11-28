import SystemE
import Elements.Book1.Prop12
import Elements.Book1.Prop47
import Elements.Book2.Prop06
import Elements.Book3.Prop03
import Elements.Book3.Prop18

namespace Elements.Book3

/--
Euclid's argument in Prop. 3.36, for the line `DCA` cutting the circle, with the center
`F`: the rectangle `AD`, `DC` and the square on `FC` make the square on `FD`
[Props. 3.3, 2.6, 1.47].
-/
theorem proposition_36_lemma : ∀ (a c d f : Point) (AC : Line) (α : Circle),
  a.onCircle α ∧ c.onCircle α ∧ distinctPointsOnLine a c AC ∧ between d c a ∧
  f.isCentre α → |(a─d)| * |(d─c)| + |(f─c)| * |(f─c)| = |(f─d)| * |(f─d)| :=
by
  euclid_intros
  by_cases (f.onLine AC)
  · -- DCA is through the center, and AC is cut in half at F [Prop. 2.6]
    euclid_apply (circle_line_intersections f a c AC α)
    euclid_apply (point_on_circle_onlyif f a c α)
    euclid_apply (Elements.Book2.proposition_6 a c f d)
    euclid_assert |(c─f)| * |(c─f)| = |(f─c)| * |(f─c)|
    euclid_assert |(d─f)| * |(d─f)| = |(f─d)| * |(f─d)|
    euclid_finish
  · -- EF perpendicular to AC [Prop. 1.12] cuts it in half [Prop. 3.3]
    euclid_apply (Elements.Book1.proposition_12 a c f AC) as g
    euclid_apply (line_from_points g f) as GF
    have : between a g c ∧ |(a─g)| = |(g─c)| ∧ ∠ a:g:f = ∟ := by
      rcases ‹_ ∨ _› with ⟨_, _⟩ | ⟨_, _⟩
      · euclid_apply (proposition_3_foot a c f g AC α)
        euclid_finish
      · euclid_apply (proposition_3_foot c a f g AC α)
        euclid_apply (right_angle_on_lines c g f a f AC GF)
        euclid_finish
    -- CD added to AC, cut in half at G: the rectangle AD, DC and the square on GC make
    -- the square on GD [Prop. 2.6]
    euclid_apply (Elements.Book2.proposition_6 a c g d)
    -- add the square on GF: those on CG, GF make that on FC, and those on DG, GF that on
    -- FD [Prop. 1.47]
    euclid_apply (line_from_points c f) as CF
    euclid_apply (line_from_points d f) as DF
    euclid_apply (right_angle_on_lines a g f c f AC GF)
    euclid_apply (right_angle_on_lines a g f d f AC GF)
    euclid_apply (Elements.Book1.proposition_47 g c f AC CF GF)
    euclid_apply (Elements.Book1.proposition_47 g d f AC DF GF)
    euclid_assert |(c─f)| * |(c─f)| = |(f─c)| * |(f─c)|
    euclid_assert |(d─f)| * |(d─f)| = |(f─d)| * |(f─d)|
    euclid_assert |(c─g)| * |(c─g)| = |(g─c)| * |(g─c)|
    euclid_assert |(d─g)| * |(d─g)| = |(g─d)| * |(g─d)|
    euclid_finish

/--
From a point `D` outside, `DCA` cutting the circle and `DB` touching it: the rectangle
`AD`, `DC` is equal to the square on `DB`.
-/
theorem proposition_36 : ∀ (a b c d f : Point) (AC DB : Line) (α : Circle),
  a.onCircle α ∧ c.onCircle α ∧ distinctPointsOnLine a c AC ∧ between d c a ∧
  DB.touchesCircleAt α b ∧ d.onLine DB ∧ f.isCentre α →
  |(a─d)| * |(d─c)| = |(d─b)| * |(d─b)| :=
by
  euclid_intros
  euclid_apply (proposition_36_lemma a c d f AC α)
  -- EBD is right [Prop. 3.18]: the squares on EB, BD make that on ED [Prop. 1.47]
  euclid_apply (proposition_18 b d f DB α)
  euclid_apply (angle_symm f b d)
  euclid_apply (line_from_points b f) as BF
  euclid_apply (line_from_points d f) as DF
  euclid_apply (Elements.Book1.proposition_47 b d f DB DF BF)
  euclid_apply (point_on_circle_onlyif f c b α)
  euclid_assert |(f─c)| * |(f─c)| = |(b─f)| * |(b─f)|
  euclid_assert |(d─f)| * |(d─f)| = |(f─d)| * |(f─d)|
  euclid_assert |(b─d)| * |(b─d)| = |(d─b)| * |(d─b)|
  euclid_finish

end Elements.Book3
