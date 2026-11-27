import SystemE
import Elements.Book1.Prop31
import Elements.Book1.Prop37


namespace Elements.Book1

-- Prop. 39 when C and D are on the same side of AB.
theorem proposition_39_side : ∀ (a b c d : Point) (AB BC AC BD CD AD : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d b c BD BC CD ∧ a.sameSide d BC ∧
  (△ a:b:c : ℝ) = (△ d:b:c) ∧ distinctPointsOnLine a d AD ∧ c.sameSide d AB →
  ¬(AD.intersectsLine BC) :=
by
  euclid_intros
  by_contra
  euclid_apply (proposition_31 a b c BC) as AE
  euclid_apply (intersection_lines AE BD) as e
  euclid_apply (line_from_points e c) as EC
  euclid_apply (proposition_37 a b c e AB BC AC BD EC AE)
  euclid_assert (△ e:b:c : ℝ) = (△ d:b:c)
  -- Omitted by Euclid: which is the greater.
  have : e ≠ d := by
    intro h
    euclid_finish
  have hcb : c ≠ b := fun h => same_side_not_on_line c d AB ‹_› (h ▸ ‹b.onLine AB›)
  rcases between_points b e d BD (by euclid_finish) with h | h | h
  · euclid_apply (sum_areas_if b d e c BD)
    have : Triangle.area △ e:d:c = 0 := by euclid_finish
    have hc := degenerated_area_if e d c BD ⟨⟨‹_›, ‹_›, ‹_›⟩, this⟩
    exact ‹BD ≠ BC› (two_points_determine_line c b BD BC ⟨⟨hc, ‹_›, hcb⟩, ‹_›, ‹_›⟩)
  · have hna : ¬(a.onLine BC) := same_side_not_on_line a d BC ‹_›
    have hae : a.sameSide e BC := same_side_of_parallel a e BC AE ⟨‹_›, ‹_›, hna, ‹_›⟩
    exact pasch_3 e b d BC ⟨h, ‹_›⟩ (same_side_trans a e d BC ⟨hae, ‹_›⟩)
  · euclid_apply (sum_areas_if b e d c BD)
    have : Triangle.area △ d:e:c = 0 := by euclid_finish
    have hc := degenerated_area_if d e c BD ⟨⟨‹_›, ‹_›, (‹e ≠ d›).symm⟩, this⟩
    exact ‹BD ≠ BC› (two_points_determine_line c b BD BC ⟨⟨hc, ‹_›, hcb⟩, ‹_›, ‹_›⟩)

theorem proposition_39 : ∀ (a b c d : Point) (AB BC AC BD CD AD : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d b c BD BC CD ∧ a.sameSide d BC ∧
  (△ a:b:c : ℝ) = (△ d:b:c) ∧ distinctPointsOnLine a d AD →
  ¬(AD.intersectsLine BC) :=
by
  euclid_intros
  by_cases c.sameSide d AB
  · euclid_apply (proposition_39_side a b c d AB BC AC BD CD AD)
    euclid_finish
  · by_cases d.onLine AB
    · -- Omitted by Euclid: D is not on AB, or △DBC and △ABC would differ by △ADC.
      by_contra
      have hcb : c ≠ b := by euclid_finish
      rcases between_points b a d AB (by euclid_finish) with h | h | h
      · euclid_apply (sum_areas_if b d a c AB)
        have : Triangle.area △ a:d:c = 0 := by euclid_finish
        have hc := degenerated_area_if a d c AB ⟨⟨‹_›, ‹_›, ‹_›⟩, this⟩
        exact ‹AB ≠ BC› (two_points_determine_line c b AB BC ⟨⟨hc, ‹_›, hcb⟩, ‹_›, ‹_›⟩)
      · exact pasch_3 a b d BC ⟨h, ‹_›⟩ ‹_›
      · euclid_apply (sum_areas_if b a d c AB)
        have : Triangle.area △ d:a:c = 0 := by euclid_finish
        have hc := degenerated_area_if d a c AB ⟨⟨‹_›, ‹_›, (‹a ≠ d›).symm⟩, this⟩
        exact ‹AB ≠ BC› (two_points_determine_line c b AB BC ⟨⟨hc, ‹_›, hcb⟩, ‹_›, ‹_›⟩)
    · -- Omitted by Euclid: the same with A and D exchanged.
      euclid_apply (triple_incidence_2 BC AB BD b c a d)
      euclid_apply (proposition_39_side d b c a BD BC CD AB AC AD)
      euclid_finish

end Elements.Book1
