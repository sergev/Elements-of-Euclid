import SystemE
import Elements.Book1.Prop23
import Elements.Book1.Prop27


namespace Elements.Book1

theorem proposition_31 : ∀ (a b c : Point) (BC : Line),
  distinctPointsOnLine b c BC ∧ ¬(a.onLine BC) →
  ∃ EF : Line, a.onLine EF ∧ ¬(EF.intersectsLine BC) :=
by
  euclid_intros
  euclid_apply (exists_point_between_points_on_line BC b c) as d
  euclid_apply (line_from_points a d) as AD
  obtain ⟨e, he, hside, hang⟩ := proposition_23' a d d a c b AD AD BC (by euclid_finish)
  -- Omitted by Euclid: E is off AD, since the angle ADC is neither nothing nor two right angles.
  have : ¬(e.onLine AD) := by
    intro h
    by_cases (between e a d)
    · euclid_apply (flat_angle_onlyif e a d)
      euclid_apply (flat_angle_if a d c)
      euclid_finish
    · euclid_apply (degenerated_angle_if a e d AD)
      euclid_finish
  have : e.sameSide b AD := hside.resolve_left this
  euclid_apply (line_from_points e a) as EF
  euclid_apply (extend_point EF e a) as f
  use EF
  constructor
  · euclid_finish
  · euclid_apply (proposition_27 e c a d EF BC AD)
    euclid_finish

end Elements.Book1
