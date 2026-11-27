import SystemE
import Elements.Book1.Prop27
import Elements.Book1.Prop29


namespace Elements.Book1

theorem proposition_30 : ∀ (AB CD EF : Line),
  AB ≠ CD ∧ CD ≠ EF ∧ EF ≠ AB ∧ ¬(AB.intersectsLine EF) ∧ ¬(CD.intersectsLine EF) →
  ¬(AB.intersectsLine CD) :=
by
  euclid_intros
  euclid_apply (line_nonempty AB) as g
  euclid_apply (exists_distincts_points_on_line CD g) as k
  euclid_apply (line_from_points g k) as GK
  euclid_apply (intersection_lines EF GK) as h
  euclid_apply (exists_distincts_points_on_line AB g) as a
  euclid_apply (extend_point AB a g) as b
  euclid_apply (point_on_line_same_side GK EF a) as e
  euclid_apply (extend_point EF e h) as f
  euclid_apply (point_on_line_same_side GK CD a) as c
  euclid_apply (extend_point CD c k) as d

  rcases between_points g h k GK (by euclid_finish) with hb | hb | hb
  · euclid_apply (proposition_29_alternate a f g h AB EF GK)
    euclid_apply (proposition_29' e f c d g h k EF CD GK)
    euclid_apply (equal_angles g a a h k AB GK)
    euclid_apply (equal_angles k g h d d GK CD)
    euclid_apply (proposition_27 a d g k AB CD GK)
    euclid_finish
  · -- Omitted by Euclid.
    euclid_apply (proposition_29_alternate d e k h CD EF GK)
    euclid_apply (proposition_29' b a f e k g h AB EF GK)
    euclid_apply (equal_angles h g k e e GK EF)
    euclid_apply (equal_angles k h g d d GK CD)
    euclid_apply (proposition_27 a d g k AB CD GK)
    euclid_finish
  · -- Omitted by Euclid.
    euclid_apply (proposition_29_alternate a f g h AB EF GK)
    euclid_apply (proposition_29' c d e f g k h CD EF GK)
    euclid_apply (equal_angles h k g f f GK EF)
    euclid_apply (equal_angles g a a h k AB GK)
    euclid_apply (proposition_27 a d g k AB CD GK)
    euclid_finish

end Elements.Book1
