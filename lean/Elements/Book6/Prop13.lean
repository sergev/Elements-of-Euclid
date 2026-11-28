import SystemE
import Elements.Book1.Prop10
import Elements.Book1.Prop11
import Elements.Book3.Prop31
import Elements.Book6.Prop08

namespace Elements.Book6

open Elements.Book5

/--
To find the straight line `xy` in mean proportion to two given straight lines `ab`, `cd`:
`ab : xy :: xy : cd`.
-/
theorem proposition_13 : ∀ (a b c d : Point),
  a ≠ b ∧ c ≠ d → ∃ x y : Point, (a─b) ∶ (x─y) ∷ (x─y) ∶ (c─d) :=
by
  euclid_intros
  -- let `ab` and `bc'`, equal to `cd`, be laid down straight-on [Prop. 1.3], and the
  -- semicircle `ADC'` drawn on `ac'`, with center `e` [Prop. 1.10]
  euclid_apply (line_from_points a b) as AC
  euclid_apply (lay_beyond a b c d AC) as c'
  euclid_apply (Elements.Book1.proposition_10 a c' AC) as e
  euclid_apply (circle_from_points e a) as α
  euclid_apply (point_on_circle_if e a c' α)
  euclid_apply (circle_points_between a c' b α)
  -- draw `BD` from `b` at right angles to `AC'` [Prop. 1.11], meeting the circle at `d'`
  euclid_apply (Elements.Book1.proposition_11 a c' b AC) as f
  euclid_apply (line_from_points b f) as BD
  euclid_apply (intersection_circle_line_extending_points α BD b f) as d'
  euclid_apply (right_angle_on_lines a b f a d' AC BD)
  euclid_apply (right_angle_on_lines a b f c' d' AC BD)
  -- `AD'C'` is an angle in a semicircle: it is a right angle [Prop. 3.31]
  euclid_apply (Elements.Book3.proposition_31 d' a c' e AC α)
  -- so `BD'` is in mean proportion to `AB`, `BC'` [Prop. 6.8 corollary]
  euclid_apply (line_from_points d' a) as DA
  euclid_apply (line_from_points c' d') as CD
  have h₁ := proposition_8_corollary d' a c' b DA AC CD BD (by euclid_finish)
  have e₁ : size (b─c') = size (c─d) := ‹_›
  exact ⟨b, d', h₁.congr rfl rfl rfl e₁⟩

end Elements.Book6
