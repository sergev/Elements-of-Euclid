import SystemE
import Elements.Book1.Prop31
import Elements.Book1.Prop38


namespace Elements.Book1

-- Two points of a line through C, on one side of a line CE, with equal triangles on CE, coincide.
theorem eq_of_equal_areas : ∀ (c d f e : Point) (L M : Line),
  distinctPointsOnLine c d L ∧ f.onLine L ∧ distinctPointsOnLine c e M ∧ L ≠ M ∧
  d.sameSide f M ∧ Triangle.area △ d:c:e = Triangle.area △ f:c:e →
  d = f :=
by
  euclid_intros
  by_contra
  rcases between_points c d f L (by euclid_finish) with h | h | h
  · euclid_apply (sum_areas_if c f d e L)
    have : Triangle.area △ d:f:e = 0 := by euclid_finish
    have he := degenerated_area_if d f e L ⟨⟨‹_›, ‹_›, ‹_›⟩, this⟩
    exact ‹L ≠ M› (two_points_determine_line c e L M ⟨⟨‹_›, he, ‹_›⟩, ‹_›, ‹_›⟩)
  · exact pasch_3 d c f M ⟨h, ‹_›⟩ ‹_›
  · euclid_apply (sum_areas_if c d f e L)
    have : Triangle.area △ f:d:e = 0 := by euclid_finish
    have he := degenerated_area_if f d e L ⟨⟨‹_›, ‹_›, (‹d ≠ f›).symm⟩, this⟩
    exact ‹L ≠ M› (two_points_determine_line c e L M ⟨⟨‹_›, he, ‹_›⟩, ‹_›, ‹_›⟩)

theorem proposition_40 : ∀ (a b c d e : Point) (AB BC AC CD DE AD : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d c e CD BC DE ∧ a.sameSide d BC ∧ b ≠ e ∧ |(b─c)| = |(c─e)| ∧
  distinctPointsOnLine a d AD ∧ (Triangle.area △ a:b:c = Triangle.area △ d:c:e) →
  ¬(AD.intersectsLine BC) :=
by
  euclid_intros
  by_contra
  euclid_apply (proposition_31 a b c BC) as AF
  euclid_apply (intersection_lines AF CD) as f
  by_cases (a = f)
  · -- Omitted by Euclid.
    euclid_apply (intersection_lines AF DE) as g
    euclid_apply (line_from_points g c) as GC
    euclid_apply (proposition_38 a b c g c e AF BC AB AC GC DE)
    have hdg := eq_of_equal_areas e d g c DE BC (by euclid_finish)
    have hAD : AD = AF := two_points_determine_line a d AD AF ⟨⟨‹_›, ‹_›, ‹_›⟩, ‹_›, hdg ▸ ‹g.onLine AF›⟩
    exact ‹¬AF.intersectsLine BC› (hAD ▸ ‹AD.intersectsLine BC›)
  · euclid_apply (line_from_points f e) as FE
    euclid_apply (proposition_38 a b c f c e AF BC AB AC CD FE)
    euclid_apply (eq_of_equal_areas c d f e CD BC)
    euclid_finish

end Elements.Book1
