import SystemE
import Elements.Book1.Prop03

namespace Elements.Book1

-- Prop. 22' with K on the same side of FE as x.
set_option maxHeartbeats 400000 in
theorem proposition_22_side : ∀ (a a' b b' c c' f e x : Point) (A B C FE : Line),
  distinctPointsOnLine a a' A ∧ distinctPointsOnLine b b' B ∧ distinctPointsOnLine c c' C ∧ distinctPointsOnLine f e FE ∧ ¬(x.onLine FE) ∧
  (|(a─a')| + |(b─b')| > |(c─c')|) ∧
  (|(a─a')| + |(c─c')| > |(b─b')|) ∧
  (|(b─b')| + |(c─c')| > |(a─a')|) →
  ∃ (k g : Point), g.onLine FE ∧ ¬(between g f e) ∧ (k.sameSide x FE) ∧
  (|(f─k)| = |(a─a')|) ∧ (|(f─g)| = |(b─b')|) ∧ (|(k─g)| = |(c─c')|) :=
by
  euclid_intros
  euclid_apply (extend_point_longer FE f e (b─b')) as e'
  euclid_apply (extend_point_longer FE f e' (c─c')) as e''
  euclid_apply (proposition_3 f e'' a a' FE A) as d
  euclid_apply (proposition_3 f e'' b b' FE B) as g
  euclid_apply (between_if f e e')
  euclid_apply (between_if f e' e'')
  euclid_apply (between_if f g e'')
  euclid_apply (proposition_3 g e'' c c' FE C) as h
  euclid_apply (circle_from_points f d) as DKL
  euclid_apply (circle_from_points g h) as KLH
  -- Euclid didn't need to explicitly note the existence of i.
  euclid_apply (intersection_circle_line_extending_points KLH FE g h) as i
  -- Omitted by Euclid: the circles meet, since D is inside KLH and I inside DKL.
  euclid_apply (point_on_circle_onlyif g h i KLH)
  have : i.insideCircle DKL := by
    by_cases (between g i f)
    · euclid_apply (between_if g i f)
      euclid_apply (point_in_circle_if f d i DKL)
      euclid_finish
    · by_cases (i = f)
      · euclid_finish
      · rcases between_points g f i FE (by euclid_finish) with hb | hb | hb
        · euclid_apply (between_if g f i)
          euclid_apply (point_in_circle_if f d i DKL)
          euclid_finish
        · euclid_apply (between_not_trans h g f i)
          euclid_finish
        · contradiction
  have : d.insideCircle KLH := by
    by_cases (between f d g)
    · euclid_apply (between_if f d g)
      euclid_apply (point_in_circle_if g h d KLH)
      euclid_finish
    · by_cases (d = g)
      · euclid_finish
      · euclid_apply (between_if f g d)
        euclid_apply (point_in_circle_if g h d KLH)
        euclid_finish
  euclid_apply (intersection_circle_circle_2 d i DKL KLH)
  euclid_apply (intersection_same_side KLH DKL x g f FE) as k
  use k, g
  euclid_apply (point_on_circle_onlyif f d k DKL)
  euclid_apply (point_on_circle_onlyif g k h KLH)
  euclid_finish

-- An extension of proposition 22 given a line and two points on it.
theorem proposition_22' : ∀ (a a' b b' c c' f e : Point) (A B C FE : Line),
  distinctPointsOnLine a a' A ∧ distinctPointsOnLine b b' B ∧ distinctPointsOnLine c c' C ∧ distinctPointsOnLine f e FE ∧
  (|(a─a')| + |(b─b')| > |(c─c')|) ∧
  (|(a─a')| + |(c─c')| > |(b─b')|) ∧
  (|(b─b')| + |(c─c')| > |(a─a')|) →
  ∃ (k g : Point), g.onLine FE ∧ ¬(between g f e) ∧
  (|(f─k)| = |(a─a')|) ∧ (|(f─g)| = |(b─b')|) ∧ (|(k─g)| = |(c─c')|) :=
by
  euclid_intros
  euclid_apply (proposition_1 f e FE) as x
  euclid_apply (proposition_22_side a a' b b' c c' f e x A B C FE) as (k, g)
  use k, g

theorem proposition_22 : ∀ (a a' b b' c c' : Point) (A B C : Line),
  distinctPointsOnLine a a' A ∧ distinctPointsOnLine b b' B ∧ distinctPointsOnLine c c' C ∧
  (|(a─a')| + |(b─b')| > |(c─c')|) ∧
  (|(a─a')| + |(c─c')| > |(b─b')|) ∧
  (|(b─b')| + |(c─c')| > |(a─a')|) →
  ∃ (k f g : Point), (|(f─k)| = |(a─a')|) ∧ (|(f─g)| = |(b─b')|) ∧ (|(k─g)| = |(c─c')|) :=
by
  euclid_intros
  euclid_apply arbitrary_point as f
  euclid_apply (distinct_points f) as e
  euclid_apply (line_from_points f e) as FE
  euclid_apply (proposition_22' a a' b b' c c' f e A B C FE) as (k, g)
  use k, f, g

end Elements.Book1
