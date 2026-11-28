import SystemE
import Elements.Book1.Prop01
import Elements.Book1.Prop03
import Elements.Book1.Prop05
import Elements.Book1.Prop20
import Elements.Book1.Prop32
import Elements.Book3.Prop26
import Elements.Book3.Prop28
import Elements.Book3.Prop30
import Elements.Book4.Lemmas
import Elements.Book4.Prop02
import Elements.Book4.Prop11

namespace Elements.Book4

/-- A point `B` of the circle within the angle `AKC` at the center divides the
circumference `AC` (C.N. 2). -/
theorem proposition_16_between : ∀ (a b c k : Point) (AK KC : Line) (α : Circle),
  k.isCentre α ∧ a.onCircle α ∧ b.onCircle α ∧ c.onCircle α ∧
  distinctPointsOnLine a k AK ∧
  distinctPointsOnLine k c KC ∧ b.sameSide c AK ∧ b.sameSide a KC →
  α.arc a c k = α.arc a b k + α.arc b c k :=
by
  euclid_intros
  euclid_apply (line_from_points k b) as KB
  euclid_apply (line_from_points a c) as AC
  euclid_apply (line_from_points a b) as AB
  euclid_apply (line_from_points b c) as BC
  -- KB cuts AC at P, within the circle, and B is beyond P
  euclid_apply (triple_incidence_1 AK KB KC k a b c)
  euclid_apply (intersection_lines_opposing a c KB AC)
  euclid_apply (intersection_lines KB AC) as p
  euclid_apply (circle_points_between a c p α)
  euclid_apply (intersection_circle_line_extending_points α KB k b) as b'
  euclid_apply (circle_line_intersections p b b' KB α)
  euclid_assert between k p b
  euclid_apply (Elements.Book3.arc_add a c b k AC α)
  euclid_assert c.sameSide k AB
  euclid_assert a.sameSide k BC
  euclid_apply (Elements.Book3.arc_side a b c k AB α)
  euclid_apply (Elements.Book3.arc_side b c a k BC α)
  euclid_finish

/-- The side `PQ` of an equilateral triangle inscribed in a circle [Props. 1.1, 4.2] cuts
off a third of the circumference. -/
theorem proposition_16_triangle : ∀ (k : Point) (α : Circle),
  k.isCentre α →
  ∃ (p q : Point) (PQ : Line), p.onCircle α ∧ q.onCircle α ∧ distinctPointsOnLine p q PQ ∧
  ¬(k.onLine PQ) ∧ α.arc p q k * 3 = α.circumference :=
by
  euclid_intros
  -- an equilateral triangle DEF [Prop. 1.1]: its angles are each a third of two right
  -- angles [Props. 1.5, 1.32]
  euclid_apply arbitrary_point as d
  euclid_apply (distinct_points d) as e
  euclid_apply (line_from_points d e) as DE
  euclid_apply (Elements.Book1.proposition_1 d e DE) as f
  euclid_apply (line_from_points e f) as EF
  euclid_apply (line_from_points f d) as FD
  euclid_apply (Elements.Book1.proposition_5' d e f DE EF FD)
  euclid_apply (Elements.Book1.proposition_5' e d f DE FD EF)
  euclid_apply (extend_point EF e f) as z
  euclid_apply (Elements.Book1.proposition_32 d e f z DE EF FD)
  -- PQR in the circle, equiangular with DEF [Prop. 4.2]
  euclid_apply (proposition_2 d e f k DE EF FD α) as (p, q, r, PQ, QR, RP)
  -- the center is within PQR [Prop. 3.31''], and the circumferences PQ, QR, RP, on the
  -- equal angles at R, P, Q, are equal [Prop. 3.26]
  euclid_apply (centre_same_side_of_acute p q k r PQ α)
  euclid_apply (centre_same_side_of_acute q r k p QR α)
  euclid_apply (centre_same_side_of_acute r p k q RP α)
  euclid_apply (point_on_circle_onlyif k p q α)
  euclid_apply (point_on_circle_onlyif k p r α)
  euclid_apply (Elements.Book3.proposition_26 r p q p q r k k PQ QR α α)
  euclid_apply (Elements.Book3.proposition_26 r p q q r p k k PQ RP α α)
  -- the three make the whole circle
  euclid_apply (points_on_both_sides p q r PQ α) as (s, s')
  euclid_apply (Elements.Book3.arc_whole p q r s PQ α)
  euclid_apply (Elements.Book3.arc_add p q r s PQ α)
  euclid_apply (Elements.Book3.arc_side p q r k PQ α)
  have := Elements.Book3.arc_symm p r q α
  have := Elements.Book3.arc_symm r q p α
  use p, q, PQ
  euclid_finish

/-- The side `AB` of an equilateral and equiangular pentagon inscribed in a circle
[Prop. 4.11] cuts off a fifth of the circumference. -/
theorem proposition_16_pentagon : ∀ (k : Point) (α : Circle),
  k.isCentre α →
  ∃ (a b : Point) (AB : Line), a.onCircle α ∧ b.onCircle α ∧ distinctPointsOnLine a b AB ∧
  ¬(k.onLine AB) ∧ α.arc a b k * 5 = α.circumference :=
by
  euclid_intros
  euclid_apply (proposition_11' k α) as (a, b, c, d, e, AB, BC, CD, DE, EA, AC, AD, BD,
    BE, CE)
  -- the circumferences AB, BC, CD, DE, EA are equal [Prop. 3.28], and make the whole
  euclid_apply (point_on_circle_onlyif k a b α)
  euclid_apply (point_on_circle_onlyif k a c α)
  euclid_apply (point_on_circle_onlyif k a d α)
  euclid_apply (point_on_circle_onlyif k a e α)
  euclid_apply (Elements.Book3.proposition_28 a b e a k k AB EA α α)
  euclid_apply (Elements.Book3.proposition_28 a b d e k k AB DE α α)
  euclid_apply (Elements.Book3.proposition_28 a b c d k k AB CD α α)
  euclid_apply (Elements.Book3.proposition_28 a b b c k k AB BC α α)
  euclid_apply (points_on_both_sides a b c AB α) as (s, s')
  euclid_apply (Elements.Book3.arc_whole a b c s AB α)
  euclid_apply (Elements.Book3.arc_add a b e s AB α)
  euclid_apply (Elements.Book3.arc_add e b d a BE α)
  euclid_apply (Elements.Book3.arc_add d b c e BD α)
  euclid_apply (Elements.Book3.arc_side a b c k AB α)
  euclid_apply (Elements.Book3.arc_side a e b k EA α)
  euclid_apply (Elements.Book3.arc_side e d b k DE α)
  euclid_apply (Elements.Book3.arc_side d c b k CD α)
  euclid_apply (Elements.Book3.arc_side c b d k BC α)
  have := Elements.Book3.arc_symm e a k α
  have := Elements.Book3.arc_symm d e k α
  have := Elements.Book3.arc_symm c d k α
  have := Elements.Book3.arc_symm b c k α
  use a, b, AB
  euclid_finish

/--
To inscribe an equilateral and equiangular fifteen-sided figure in a given circle `α`,
with center `k`: its side `BE` cuts off a fifteenth of the circumference (away from `C`).
-/
theorem proposition_16 : ∀ (k : Point) (α : Circle),
  k.isCentre α →
  ∃ (b e c : Point), insertedInto b e α ∧ c.onCircle α ∧ b ≠ e ∧ c ≠ b ∧ c ≠ e ∧
  α.arc b e c * 15 = α.circumference :=
by
  euclid_intros
  -- AB, the side of a pentagon inscribed in the circle [Prop. 4.11], is a fifth of it
  euclid_apply (proposition_16_pentagon k α) as (a, b, AB)
  -- AC, the side of an equilateral triangle [Prop. 4.2], equal to PQ, a third: inserted
  -- from A [Prop. 4.1], on B's side of the diameter through A
  euclid_apply (proposition_16_triangle k α) as (p, q, PQ)
  euclid_apply (line_from_points a k) as AK
  euclid_apply (intersection_circle_line_extending_points α AK k a) as a'
  euclid_apply (line_from_points k p) as KP
  euclid_apply (line_from_points k q) as KQ
  euclid_apply (Elements.Book1.proposition_20 k p q KP PQ KQ)
  euclid_apply (point_on_circle_onlyif k a p α)
  euclid_apply (point_on_circle_onlyif k a q α)
  euclid_apply (point_on_circle_onlyif k a a' α)
  euclid_apply (between_if a' k a)
  euclid_apply (Elements.Book1.proposition_3 a a' p q AK PQ) as m
  euclid_apply (circle_from_points a m) as β
  euclid_apply (circle_points_between a a' m α)
  euclid_apply (intersection_circle_circle_2 a m α β)
  euclid_apply (intersection_same_side α β b k a AK) as c
  euclid_apply (point_on_circle_onlyif a m c β)
  euclid_apply (line_from_points a c) as AC
  euclid_apply (point_on_circle_onlyif k a c α)
  euclid_apply (Elements.Book3.proposition_28 a c p q k k AC PQ α α)
  -- the circumference ABC, a third, is made of five fifteenths, and AB of three: the
  -- remainder BC of two. Missed by Euclid: B is within the angle AKC, the fifth AB
  -- being less than the third AC.
  euclid_apply (line_from_points k c) as KC
  euclid_apply (Elements.Book3.arc_pos a b k AB α)
  have : b.sameSide a KC := by
    by_cases (b.onLine KC)
    · exfalso
      euclid_apply (eq_of_same_ray b c k KC)
      euclid_finish
    · by_cases (b.sameSide a KC)
      · assumption
      · exfalso
        euclid_apply (line_from_points k b) as KB
        euclid_apply (triple_incidence_2 AK KC KB k a c b)
        euclid_apply (proposition_16_between a c b k AK KB α)
        euclid_apply (line_from_points c b) as CB
        euclid_apply (Elements.Book3.arc_pos c b k CB α)
        euclid_finish
  euclid_apply (proposition_16_between a b c k AK KC α)
  -- BC cut in half at E [Prop. 3.30]: BE is a fifteenth
  euclid_apply (line_from_points b c) as BC
  euclid_apply (points_on_both_sides b c k BC α) as (x, x')
  euclid_apply (Elements.Book3.proposition_30 b c x k BC α) as e
  euclid_apply (Elements.Book3.arc_add b c e k BC α)
  use b, e, c
  euclid_finish

/-
Euclid's remarks are left out: that straight lines equal to `BE`, inserted continuously
into the circle [Prop. 4.1], make the fifteen-sided figure; and that it can be
circumscribed about a circle, and a circle inscribed in and circumscribed about it,
"similarly to the pentagon".
-/

end Elements.Book4
