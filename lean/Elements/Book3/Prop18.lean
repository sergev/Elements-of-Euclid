import SystemE
import Elements.Book1.Prop12
import Elements.Book1.Prop17
import Elements.Book1.Prop19

namespace Elements.Book3

/-- The radius `FC` to the point of contact of a tangent `DE` is perpendicular to it. -/
theorem proposition_18 : ∀ (c d f : Point) (DE : Line) (α : Circle),
  DE.touchesCircleAt α c ∧ f.isCentre α ∧ d.onLine DE ∧ d ≠ c → ∠ f:c:d = ∟ :=
by
  euclid_intros
  by_contra
  -- if not, let FG be drawn perpendicular to DE [Prop. 1.12]
  euclid_apply (Elements.Book1.proposition_12 c d f DE) as g
  euclid_apply (line_from_points f g) as FG
  euclid_apply (line_from_points f c) as FC
  -- G is not C, since FCD is not right
  have : g ≠ c ∧ ∠ c:g:f = ∟ := by
    rcases ‹_ ∨ _› with ⟨_, _⟩ | ⟨_, _⟩
    · euclid_finish
    · by_cases (g = c)
      · exfalso
        euclid_finish
      · euclid_apply (right_angle_on_lines d g f c f DE FG)
        euclid_finish
  euclid_assert ¬(f.onLine DE)
  euclid_assert ¬(g.onLine FC)
  -- the angle FGC is right, so FCG is acute [Prop. 1.17], and FC is greater than FG
  -- [Prop. 1.19]; but FC = FB, the lesser than the greater
  euclid_apply (Elements.Book1.proposition_17 f g c FG DE FC)
  euclid_apply (Elements.Book1.proposition_19 f g c FG DE FC)
  euclid_apply (point_in_circle_if f c g α)
  euclid_finish

end Elements.Book3
