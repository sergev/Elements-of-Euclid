import SystemE
import Elements.Book1.Prop01
import Elements.Book1.Prop03
import Elements.Book1.Prop05
import Elements.Book1.Prop07
import Elements.Book1.Prop08

namespace Elements.Book1

theorem proposition_9 : ∀ (a b c : Point) (AB AC : Line),
  formRectilinearAngle b a c AB AC ∧ AB ≠ AC →
  ∃ f : Point, (f.sameSide c AB) ∧ (f.sameSide b AC) ∧ (∠ b:a:f = ∠ c:a:f) :=
by
  euclid_intros
  euclid_apply (point_between_points_shorter_than AB a b (a─c)) as d
  euclid_apply (proposition_3 a c a d AC AB) as e
  euclid_apply (line_from_points d e) as DE
  euclid_apply (proposition_1' d e a DE) as f
  euclid_apply (line_from_points f e) as FE
  euclid_apply (line_from_points f d) as FD
  euclid_apply (line_from_points a f) as AF
  use f
  have : ¬(f.onLine AB) := by  -- Omitted by Euclid.
    euclid_intros
    euclid_apply (proposition_5' f d e AB DE FE)
    euclid_apply (proposition_5 a d e b c AB DE AC)
    euclid_finish
  have : ¬(f.onLine AC) := by  -- Omitted by Euclid.
    euclid_intros
    euclid_apply (proposition_5' f e d AC DE FD)
    euclid_apply (proposition_5 a d e b c AB DE AC)
    euclid_finish
  euclid_apply (proposition_8 a d f a e f AB FD AF AC FE AF)
  euclid_apply (intersection_lines AF DE) as g
  -- Missed by Euclid: AF cuts DE in half at G, so F is within the angle.
  euclid_apply (equal_angles a d d f g AB AF)
  euclid_apply (equal_angles a e e f g AC AF)
  euclid_apply (proposition_4 a d g a e g AB DE AF AC DE AF)
  euclid_assert between d g e
  euclid_apply (equal_angles a d b f f AB AF)
  euclid_apply (equal_angles a e c f f AC AF)
  euclid_finish

end Elements.Book1
