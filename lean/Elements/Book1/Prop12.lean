import SystemE
import Elements.Book1.Prop08
import Elements.Book1.Prop10

namespace Elements.Book1

theorem proposition_12 : ∀ (a b c : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ ¬(c.onLine AB) →
  ∃ h : Point, h.onLine AB ∧ (∠ a:h:c = ∟ ∨ ∠ b:h:c = ∟) :=
by
  euclid_intros
  euclid_apply (exists_point_opposite AB c) as d
  euclid_apply (circle_from_points c d) as EFG
  -- Omitted by Euclid: the circle cuts AB, since CD crosses AB inside it.
  euclid_apply (line_from_points c d) as CD
  euclid_apply (intersection_lines CD AB) as m
  euclid_apply (between_if c m d)
  euclid_apply (point_in_circle_if c d m EFG)
  euclid_apply (intersection_circle_line_2 m EFG AB)
  euclid_apply (intersections_circle_line EFG AB) as (e, g)
  euclid_apply (proposition_10 e g AB) as h
  euclid_apply (line_from_points c g) as CG
  euclid_apply (line_from_points c h) as CH
  euclid_apply (line_from_points c e) as CE
  use h
  euclid_apply (proposition_8 h c g h c e CH CG AB CH CE AB)
  euclid_apply (perpendicular_if e g h c AB)
  -- Omitted by Euclid: the right angle at H is on the side of A, or of B if H is A.
  by_cases (h = a)
  · by_cases (between b h e)
    · euclid_apply (equal_angles h b g c c AB CH)
      refine ⟨?_, Or.inr ?_⟩ <;> euclid_finish
    · euclid_apply (equal_angles h b e c c AB CH)
      refine ⟨?_, Or.inr ?_⟩ <;> euclid_finish
  · by_cases (between a h e)
    · euclid_apply (equal_angles h a g c c AB CH)
      refine ⟨?_, Or.inl ?_⟩ <;> euclid_finish
    · euclid_apply (equal_angles h a e c c AB CH)
      refine ⟨?_, Or.inl ?_⟩ <;> euclid_finish

end Elements.Book1
