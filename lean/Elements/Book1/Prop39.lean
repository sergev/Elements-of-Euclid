import SystemE
import Elements.Book1.Prop31
import Elements.Book1.Prop37


namespace Elements.Book1

theorem proposition_39 : ∀ (a b c d : Point) (AB BC AC BD CD AD : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d b c BD BC CD ∧ a.sameSide d BC ∧
  (△ a:b:c : ℝ) = (△ d:b:c) ∧ distinctPointsOnLine a d AD →
  ¬(AD.intersectsLine BC) :=
by
  euclid_intros
  by_contra
  by_cases c.sameSide d AB
  · euclid_apply (proposition_31 a b c BC) as AE
    euclid_apply (intersection_lines AE BD) as e
    euclid_apply (line_from_points e c) as EC
    euclid_apply (proposition_37 a b c e AB BC AC BD EC AE)
    euclid_assert (△ e:b:c : ℝ) = (△ d:b:c)
    euclid_finish
  · -- Omitted by Euclid.
    euclid_apply (proposition_31 d b c BC) as DE
    euclid_apply (intersection_lines DE AB) as e
    euclid_apply (line_from_points e c) as EC
    euclid_apply (proposition_37 d b c e BD BC CD AB EC DE)
    -- E is on AB; on either side of A, △EBC and △ABC differ by △AEC, so E = A.
    by_cases (between a e b)
    · euclid_apply (sum_areas_if a b e c AB)
      euclid_finish
    · euclid_assert (between e a b)
      euclid_apply (sum_areas_if e b a c AB)
      euclid_finish

end Elements.Book1
