import SystemE
import Elements.Book1.Prop11

namespace Elements.Book1

theorem proposition_13 : ∀ (a b c d : Point) (AB CD : Line),
  AB ≠ CD ∧ distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ between d b c →
  ∠ c:b:a + ∠ a:b:d = ∟ + ∟ :=
by
  euclid_intros
  by_cases ∠ c:b:a = ∠ a:b:d
  · euclid_apply (perpendicular_if c d b a CD)
    euclid_finish
  · euclid_apply (proposition_11' d c b a CD) as e
    euclid_apply (line_from_points b e) as BE
    euclid_apply (perpendicular_onlyif d c b e CD)
    by_cases a.onLine BE
    · -- Omitted by Euclid.
      euclid_apply (equal_angles b c c e a CD BE)
      euclid_apply (equal_angles b d d e a CD BE)
      euclid_finish
    · by_cases a.sameSide d BE
      · euclid_apply (sum_angles_onlyif b d e a CD BE)
        euclid_apply (sum_angles_onlyif b c a e CD AB)
        euclid_finish
      · -- Omitted by Euclid.
        euclid_apply (sum_angles_onlyif b c e a CD BE)
        euclid_apply (sum_angles_onlyif b a d e AB CD)
        euclid_finish

end Elements.Book1
