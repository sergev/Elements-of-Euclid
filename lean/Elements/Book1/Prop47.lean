import SystemE
import Elements.Book1.Prop04
import Elements.Book1.Prop13
import Elements.Book1.Prop14
import Elements.Book1.Prop16
import Elements.Book1.Prop17
import Elements.Book1.Prop30
import Elements.Book1.Prop31
import Elements.Book1.Prop41
import Elements.Book1.Prop46

namespace Elements.Book1

set_option maxHeartbeats 400000 in
theorem proposition_47 : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (∠ b:a:c : ℝ) = ∟ →
  |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| :=
by
  euclid_intros
  euclid_apply (proposition_46' b a c AB) as (f, g, FG, BF, AG)
  euclid_apply (proposition_46' a c b AC) as (h, k, HK, AH, CK)
  euclid_apply (proposition_46' b c a BC) as (d, e, DE, BD, CE)

  -- Missed by Euclid.
  have : (∠ a:b:c : ℝ) < ∟ := by
    euclid_apply (proposition_17 c a b AC AB BC)
    euclid_finish

  -- Missed by Euclid.
  have : ¬(d.onLine AB) := by
    by_contra
    euclid_apply (proposition_13 c b a d BC AB)
    euclid_finish

  -- Missed by Euclid.
  have : (d.sameSide c AB) := by
    by_contra
    euclid_apply (extend_point AB a b) as b'
    euclid_apply (proposition_16 c a b b' AC AB BC)
    euclid_assert (∠ c:b:b' : ℝ) > ∟
    euclid_apply (triple_incidence_2 BC AB BD b c b' d)
    euclid_apply (sum_angles_onlyif b c d b' BC BD)
    euclid_finish

  -- Missed by Euclid.
  have : (∠ a:c:b : ℝ) < ∟ := by
    euclid_apply (proposition_17 b c a BC AC AB)
    euclid_finish

  -- Missed by Euclid.
  have : ¬(e.onLine AC) := by
    by_contra
    euclid_apply (proposition_13 b c a e BC AC)
    euclid_finish

  -- Missed by Euclid.
  have : (e.sameSide b AC) := by
    by_contra
    euclid_apply (extend_point AC a c) as c'
    euclid_apply (proposition_16 b a c c' AB AC BC)
    euclid_assert (∠ b:c:c' : ℝ) > ∟
    euclid_apply (triple_incidence_2 BC AC CE c b c' e)
    euclid_apply (sum_angles_onlyif c b e c' BC CE)
    euclid_finish

  euclid_apply (proposition_31 a b d BD) as AL
  euclid_apply (proposition_30 AL CE BD)
  euclid_apply (intersection_lines AL DE) as l
  euclid_apply (intersection_lines AL BC) as l'
  euclid_apply (line_from_points a d) as AD
  euclid_apply (line_from_points f c) as FC
  euclid_apply (proposition_14 b a c g AB AC AG)
  euclid_apply (proposition_14 c a b h AC AB AH)
  euclid_assert ((∠ d:b:a : ℝ) = ∠ f:b:c)
  euclid_assert ((∠ c:b:a : ℝ) + ∟ = ∠ c:b:f)
  euclid_apply (proposition_4 b d a b c f BD AD AB BC FC BF)
  euclid_assert ((Triangle.area △ a:b:d) = Triangle.area △ b:c:f)
  euclid_apply (proposition_41 l' b d l a AL BD BC DE AB AD)
  euclid_apply (proposition_41 g f b a c AG BF FG AB FC BC)
  euclid_assert ((Triangle.area △ g:f:b : ℝ) + (Triangle.area △ g:b:a) = (Triangle.area △ l':b:d) + (Triangle.area △ l':d:l))
  euclid_apply (line_from_points a e) as AE
  euclid_apply (line_from_points b k) as BK
  euclid_apply sum_angles_onlyif c e a b CE AC
  euclid_apply sum_angles_onlyif c k b a CK BC
  euclid_assert ((∠ e:c:a : ℝ) = (∠ k:c:b))
  euclid_apply (proposition_4 c e a c b k CE AE AC BC BK CK)
  euclid_assert ((Triangle.area △ a:c:e : ℝ) = Triangle.area △ c:b:k)
  euclid_apply (proposition_41 l' c e l a AL CE BC DE AC AE)
  euclid_apply (proposition_41 h k c a b AH CK HK AC BK BC)
  euclid_assert ((Triangle.area △ k:c:a : ℝ) + (Triangle.area △ k:a:h) = (Triangle.area △ l':c:e) + (Triangle.area △ l':e:l))
  euclid_apply (rectangle_area b c d e BC DE BD CE)
  euclid_apply (rectangle_area b a f g AB FG BF AG)
  euclid_apply (rectangle_area a c h k AC HK AH CK)
  -- Missed by Euclid: L lies between D and E, since AL is parallel to BD and CE.
  euclid_assert a.sameSide c BD
  euclid_assert a.sameSide e BD
  euclid_assert l.sameSide e BD
  euclid_assert a.sameSide b CE
  euclid_assert a.sameSide d CE
  euclid_assert l.sameSide d CE
  have : between d l e := by
    rcases between_points d l e DE (by euclid_finish) with h | h | h
    · exact h
    · exact absurd ‹l.sameSide e BD› (pasch_3 l d e BD ⟨h, ‹_›⟩)
    · exact absurd ‹l.sameSide d CE› (pasch_3 l e d CE ⟨(between_symm d e l h).1, ‹_›⟩)
  euclid_apply sum_parallelograms_area b c d e l' l BC DE BD CE
  euclid_apply parallelogram_area b l' d l BC DE BD AL
  euclid_assert ((Triangle.area △ b:d:e : ℝ) + (Triangle.area △ b:e:c) = (Triangle.area △ g:f:b) + (Triangle.area △ g:b:a) + (Triangle.area △ k:c:a) + (Triangle.area △ k:a:h))
  -- The squares' sides
  have hbd : |(b─d)| = |(b─c)| := by euclid_finish
  have hbf : |(b─f)| = |(b─a)| := by euclid_finish
  have hah : |(a─h)| = |(a─c)| := by euclid_finish
  have : |(b─c)| * |(b─d)| = |(b─c)| * |(b─c)| := by rw [hbd]
  have : |(b─a)| * |(b─f)| = |(b─a)| * |(b─a)| := by rw [hbf]
  have : |(a─c)| * |(a─h)| = |(a─c)| * |(a─c)| := by rw [hah]
  euclid_finish

end Elements.Book1
