import SystemE
import Elements.Book1.Prop11
import Elements.Book1.Prop13
import Elements.Book1.Prop23
import Elements.Book1.Prop32
import Elements.Book3.Prop18
import Elements.Book4.Lemmas

namespace Elements.Book4

/--
The quadrilateral `AMBK`, of the tangents at `A`, `B` meeting at `M` and the radii `KA`,
`KB`: its angles at `K` and `M` make two right angles, since those at `A` and `B` are
right [Props. 3.18, 1.32].
-/
theorem proposition_3_lemma : ∀ (a b k m : Point) (TA TB AK BK : Line) (α : Circle),
  k.isCentre α ∧ a.onCircle α ∧ b.onCircle α ∧ TA.touchesCircleAt α a ∧
  TB.touchesCircleAt α b ∧ distinctPointsOnLine a k AK ∧ distinctPointsOnLine b k BK ∧
  ¬(b.onLine AK) ∧ m.onLine TA ∧ m.onLine TB ∧ m.sameSide b AK ∧ m.sameSide a BK →
  ∠ a:k:b + ∠ a:m:b = ∟ + ∟ :=
by
  euclid_intros
  euclid_apply (Elements.Book3.proposition_18 a m k TA α)
  euclid_apply (Elements.Book3.proposition_18 b m k TB α)
  -- AMBK is divided into two triangles by KM [Prop. 1.32]
  euclid_apply (line_from_points k m) as KM
  euclid_apply (extend_point AK k a) as x
  euclid_apply (extend_point BK k b) as y
  euclid_apply (Elements.Book1.proposition_32 m k a x KM AK TA)
  euclid_apply (Elements.Book1.proposition_32 m k b y KM BK TB)
  euclid_apply (sum_angles_onlyif k a b m AK BK)
  euclid_apply (centre_same_side_of_touches a b k TA α)
  euclid_apply (centre_same_side_of_touches b a k TB α)
  euclid_apply (sum_angles_onlyif m a b k TA TB)
  euclid_finish

/-- Rays `KA`, `KB`, `KC` with `A`, `C` on either side of `KB` and the angles at `K` from
`KB` together greater than two right angles: `B`, `C` are on either side of `KA`. -/
theorem proposition_3_sides : ∀ (a b c k : Point) (AK KB CK : Line),
  distinctPointsOnLine k a AK ∧ distinctPointsOnLine k b KB ∧
  distinctPointsOnLine k c CK ∧
  ¬(b.onLine AK) ∧ ¬(b.onLine CK) ∧ |(k─a)| = |(k─c)| ∧ a.opposingSides c KB ∧
  ∟ + ∟ < ∠ a:k:b + ∠ b:k:c →
  b.opposingSides c AK :=
by
  euclid_intros
  by_cases (c.onLine AK)
  · exfalso
    by_cases (between a k c)
    · euclid_apply (Elements.Book1.proposition_13 b k a c KB AK)
      euclid_finish
    · euclid_apply (eq_of_same_ray a c k AK)
      euclid_finish
  · by_cases (b.sameSide c AK)
    · exfalso
      euclid_apply (triple_incidence_2 AK KB CK k a b c)
      euclid_apply (sum_angles_onlyif k a c b AK CK)
      have := (angle_range (Angle.ofPoints a k c)).2
      linarith
    · euclid_finish

/-- To circumscribe about a circle `α`, with center `k`, a triangle `LMN` equiangular with
a given triangle `DEF`; its sides touch the circle at `A`, `B`, `C`. -/
theorem proposition_3 : ∀ (d e f k : Point) (DE EF FD : Line) (α : Circle),
  formTriangle d e f DE EF FD ∧ k.isCentre α →
  ∃ (l m n a b c : Point) (LM MN NL : Line), formTriangle l m n LM MN NL ∧
  circumscribedTriangle l m n LM MN NL a b c α ∧ equiangularTriangles l m n d e f :=
by
  euclid_intros
  -- let EF be produced both ways, to G and H
  euclid_apply (extend_point EF f e) as g
  euclid_apply (extend_point EF e f) as h
  -- KB drawn at random; BKA equal to DEG, and BKC to DFH, on either side [Prop. 1.23]
  euclid_apply (exists_point_on_circle α) as b
  euclid_apply (line_from_points k b) as KB
  euclid_apply (Elements.Book1.proposition_11_end k b KB) as x
  euclid_apply (exists_point_opposite KB x) as x'
  euclid_apply (Elements.Book1.proposition_23_side k b e d g x KB DE EF) as a'
  euclid_apply (Elements.Book1.proposition_23_side k b f d h x' KB FD EF) as c'
  euclid_apply (line_from_points k a') as AK
  euclid_apply (line_from_points k c') as CK
  euclid_apply (extend_point AK a' k) as a₀
  euclid_apply (extend_point CK c' k) as c₀
  euclid_apply (intersection_circle_line_extending_points α AK k a₀) as a
  euclid_apply (intersection_circle_line_extending_points α CK k c₀) as c
  euclid_apply (equal_angles k a' a b b AK KB)
  euclid_apply (equal_angles k c' c b b CK KB)
  euclid_apply (Elements.Book1.proposition_13 d e f g DE EF)
  euclid_apply (Elements.Book1.proposition_13 d f e h FD EF)
  euclid_apply (Elements.Book1.proposition_32 d e f h DE EF FD)
  euclid_assert a.opposingSides c KB
  euclid_assert ¬(b.onLine AK)
  euclid_assert ¬(b.onLine CK)
  -- Missed by Euclid: B and C are on either side of KA, and A and B of KC, since the
  -- angles BKA, BKC are together greater than two right angles.
  euclid_apply (point_on_circle_onlyif k a c α)
  euclid_apply (proposition_3_sides a b c k AK KB CK)
  euclid_apply (proposition_3_sides c b a k CK KB AK)
  -- LAM, MBN, NCL touching the circle at A, B, C; missed by Euclid: they meet
  -- (Post. 5)
  euclid_apply (exists_tangent a k α) as LM
  euclid_apply (exists_tangent b k α) as MN
  euclid_apply (exists_tangent c k α) as NL
  euclid_apply (line_from_points a b) as AB
  euclid_apply (line_from_points b c) as BC
  euclid_apply (line_from_points c a) as CA
  euclid_apply (tangents_meet a b k LM MN AB AK KB α) as m
  euclid_apply (tangents_meet b c k MN NL BC KB CK α) as n
  euclid_apply (tangents_meet c a k NL LM CA CK AK α) as l
  -- the angles at K and M of AMBK make two right angles, and so do DEG and DEF
  -- [Prop. 1.13]; AKB is equal to DEG, so AMB to DEF. Similarly BNC to DFE.
  euclid_apply (proposition_3_lemma a b k m LM MN AK KB α)
  euclid_apply (proposition_3_lemma b c k n MN NL KB CK α)
  euclid_assert between l a m
  euclid_assert between m b n
  euclid_assert between n c l
  euclid_apply (equal_angles m a l b n LM MN)
  euclid_apply (equal_angles n b m c l MN NL)
  -- the remaining MLN is equal to EDF [Prop. 1.32]
  euclid_apply (extend_point MN m n) as z
  euclid_apply (Elements.Book1.proposition_32 l m n z LM MN NL)
  use l, m, n, a, b, c, LM, MN, NL
  euclid_finish

end Elements.Book4
