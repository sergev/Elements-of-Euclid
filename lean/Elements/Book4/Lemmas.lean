import SystemE
import Elements.Book1.Prop05
import Elements.Book1.Prop10
import Elements.Book1.Prop11
import Elements.Book1.Prop12
import Elements.Book1.Prop13
import Elements.Book1.Prop23
import Elements.Book1.Prop27
import Elements.Book1.Prop29
import Elements.Book1.Prop32
import Elements.Book3.Prop16
import Elements.Book3.Prop18
import Elements.Book3.Prop31

/-
Facts Book 4 takes from the figure, and a few constructions it repeats: tangents and
where they meet, perpendiculars and where they fall, and the order of points around a
circle, which makes a figure inscribed in it convex.
-/

namespace Elements.Book4

/-- A side of a right angle is not on the other side's line. -/
theorem not_on_line_of_right_angle : ∀ (x y z : Point) (L : Line),
  distinctPointsOnLine y z L ∧ x ≠ y ∧ ∠ x:y:z = ∟ → ¬(x.onLine L) :=
by
  euclid_intros
  have := Elements.Book1.right_angle_pos
  by_cases (between x y z)
  · euclid_apply (flat_angle_onlyif x y z)
    euclid_finish
  · euclid_apply (degenerated_angle_if y x z L)
    euclid_finish

/-- An angle whose sides are on different lines is less than two right angles. -/
theorem angle_lt_flat : ∀ (a b c : Point) (L : Line),
  distinctPointsOnLine b c L ∧ ¬(a.onLine L) → ∠ a:b:c < ∟ + ∟ :=
by
  euclid_intros
  rcases lt_or_eq_of_le (angle_range (Angle.ofPoints a b c)).2 with h | h
  · exact h
  · exfalso
    euclid_apply (flat_angle_if a b c)
    euclid_finish

/-- A line cutting a circle through a point `a` on it meets it again. -/
theorem other_intersection : ∀ (a : Point) (L : Line) (α : Circle),
  a.onCircle α ∧ a.onLine L ∧ L.intersectsCircle α →
  ∃ c : Point, c.onCircle α ∧ c.onLine L ∧ c ≠ a :=
by
  euclid_intros
  euclid_apply (intersections_circle_line α L) as (p, q)
  by_cases (p = a)
  · use q
    euclid_finish
  · use p

/-- A chord `bd` has points of the circle on either side, `x` across from `f`, `y` on its
side. -/
theorem points_on_both_sides : ∀ (b d f : Point) (BD : Line) (α : Circle),
  distinctPointsOnLine b d BD ∧ b.onCircle α ∧ d.onCircle α ∧ ¬(f.onLine BD) →
  ∃ (x y : Point), x.onCircle α ∧ y.onCircle α ∧ x.opposingSides f BD ∧ y.sameSide f BD :=
by
  euclid_intros
  euclid_apply (Elements.Book1.proposition_10 b d BD) as m
  euclid_apply (circle_points_between b d m α)
  euclid_apply (line_from_points m f) as MF
  euclid_apply (intersection_circle_line_extending_points α MF m f) as x
  euclid_apply (intersection_circle_line_extending_points α MF m x) as y
  use x, y
  euclid_finish

/-- A line touching a circle at a given point `a`: at right angles to the radius `ka`
[Props. 1.11, 3.16 corollary]. -/
theorem exists_tangent : ∀ (a k : Point) (α : Circle),
  k.isCentre α ∧ a.onCircle α → ∃ T : Line, T.touchesCircleAt α a :=
by
  euclid_intros
  euclid_apply (line_from_points k a) as KA
  euclid_apply (Elements.Book1.proposition_11_end a k KA) as h
  euclid_apply (line_from_points a h) as T
  euclid_apply (intersection_circle_line_extending_points α KA k a) as a'
  euclid_apply (right_angle_on_lines k a h a' h KA T)
  euclid_apply (Elements.Book3.proposition_16_corollary a a' k h T α)
  use T

/-- The center is on the circle's side of a line touching it. -/
theorem centre_same_side_of_touches : ∀ (a b k : Point) (L : Line) (α : Circle),
  L.touchesCircleAt α a ∧ k.isCentre α ∧ b.onCircle α ∧ b ≠ a → k.sameSide b L :=
by
  euclid_intros
  by_contra
  euclid_apply (line_from_points k b) as KB
  euclid_apply (intersection_lines_opposing k b L KB)
  euclid_apply (intersection_lines L KB) as p
  euclid_apply (circle_points_between k b p α)
  euclid_finish

/-- A point of `L`, through `a`, on the other side of `M` from `k`. -/
theorem point_on_line_opposite : ∀ (a k : Point) (L M : Line),
  a.onLine L ∧ a.onLine M ∧ L ≠ M ∧ ¬(k.onLine M) →
  ∃ p : Point, p.onLine L ∧ p.opposingSides k M :=
by
  euclid_intros
  euclid_apply (exists_distincts_points_on_line L a) as q
  by_cases (q.sameSide k M)
  · euclid_apply (extend_point L q a) as p
    use p
    euclid_finish
  · use q
    euclid_finish

/--
The lines touching a circle at the ends `a`, `b` of a chord, not a diameter, meet at `m`
(Post. 5), across the chord from the center `k`, and within the angle `akb`.
-/
theorem tangents_meet : ∀ (a b k : Point) (TA TB AB AK BK : Line) (α : Circle),
  k.isCentre α ∧ a.onCircle α ∧ b.onCircle α ∧ TA.touchesCircleAt α a ∧
  TB.touchesCircleAt α b ∧ distinctPointsOnLine a b AB ∧ distinctPointsOnLine a k AK ∧
  distinctPointsOnLine b k BK ∧ ¬(b.onLine AK) →
  ∃ m : Point, m.onLine TA ∧ m.onLine TB ∧ m.opposingSides k AB ∧ m.sameSide b AK ∧
  m.sameSide a BK :=
by
  euclid_intros
  euclid_apply (point_on_line_opposite a k TA AB) as p
  euclid_apply (point_on_line_opposite b k TB AB) as r
  -- the angles at `a`, `b` with the radii are right [Prop. 3.18]
  euclid_apply (Elements.Book3.proposition_18 a p k TA α)
  euclid_apply (Elements.Book3.proposition_18 b r k TB α)
  euclid_apply (centre_same_side_of_touches a b k TA α)
  euclid_apply (centre_same_side_of_touches b a k TB α)
  euclid_apply (sum_angles_onlyif a k p b AK TA)
  euclid_apply (sum_angles_onlyif b k r a BK TB)
  -- the angles `kab`, `kba` are equal [Prop. 1.5]
  euclid_apply (point_on_circle_onlyif k a b α)
  euclid_apply (Elements.Book1.proposition_5' k a b AK AB BK)
  euclid_apply (lines_intersect p a b r TA AB TB) as m
  use m
  euclid_finish

/-- A line at right angles to the radius `de` at its end touches the circle
[Prop. 3.16 corollary]. -/
theorem touches_of_perpendicular : ∀ (d e x : Point) (L : Line) (α : Circle),
  d.isCentre α ∧ e.onCircle α ∧ e.onLine L ∧ x.onLine L ∧ x ≠ e ∧ ¬(d.onLine L) ∧
  ∠ x:e:d = ∟ →
  L.touchesCircleAt α e :=
by
  euclid_intros
  euclid_apply (line_from_points d e) as DE
  euclid_apply (intersection_circle_line_extending_points α DE d e) as e'
  euclid_apply (right_angle_on_lines x e d x e' L DE)
  euclid_apply (Elements.Book3.proposition_16_corollary e e' d x L α)
  euclid_finish

/-- The perpendicular from `d` falls on the ray from `b` through `a` when the angle at
`b` is less than a right angle [Props. 1.13, 1.32]. -/
theorem foot_on_ray : ∀ (a b d e : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ ¬(d.onLine AB) ∧ e.onLine AB ∧ e ≠ b ∧ ∠ b:e:d = ∟ ∧
  ∠ a:b:d < ∟ → ¬(between e b a) :=
by
  euclid_intros
  euclid_apply (line_from_points b d) as BD
  euclid_apply (line_from_points e d) as ED
  euclid_apply (Elements.Book1.proposition_13 d b a e BD AB)
  euclid_apply (extend_point AB e b) as z
  euclid_apply (Elements.Book1.proposition_32 d e b z ED AB BD)
  euclid_finish

/-- The perpendicular from `d` to `AB` [Prop. 1.12] falls on the ray from `b` through `a`
when the angle at `b` is less than a right angle. -/
theorem perpendicular_foot : ∀ (a b d : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ ¬(d.onLine AB) ∧ ∠ a:b:d < ∟ →
  ∃ e : Point, e.onLine AB ∧ e ≠ b ∧ ¬(between e b a) ∧ ∠ b:e:d = ∟ :=
by
  euclid_intros
  euclid_apply (Elements.Book1.proposition_12 a b d AB) as h
  have : h ≠ b ∧ ∠ b:h:d = ∟ := by
    rcases ‹h ≠ a ∧ ∠ a:h:d = ∟ ∨ h ≠ b ∧ ∠ b:h:d = ∟› with ⟨_, _⟩ | ⟨_, _⟩
    · by_cases (h = b)
      · exfalso
        euclid_finish
      · euclid_apply (right_angle_move a h d b AB)
        euclid_finish
    · euclid_finish
  euclid_apply (foot_on_ray a b d h AB)
  use h

/-- A point `e` of `AB` on `b`'s side of a line through `a`, and on `a`'s side of a line
through `b`, is between `a` and `b`. -/
theorem between_of_same_sides : ∀ (a b e : Point) (AB M N : Line),
  distinctPointsOnLine a b AB ∧ e.onLine AB ∧ a.onLine M ∧ b.onLine N ∧
  e.sameSide b M ∧ e.sameSide a N → between a e b :=
by
  euclid_intros
  euclid_apply (between_points a e b AB)
  rcases ‹between a e b ∨ between e a b ∨ between a b e› with h | h | h
  · exact h
  · exfalso
    euclid_apply (pasch_3 e a b M)
    euclid_finish
  · exfalso
    euclid_apply (pasch_3 a b e N)
    euclid_finish

/--
Lines `L`, `M` at right angles to `AB` at `d` and to `AC` at `e` meet (Post. 5): if they
did not, `AB` would meet `M` at right angles too [Prop. 1.29], and the triangle on `AB`,
`AC` and `M` would have two right angles [Prop. 1.32].
-/
theorem perpendiculars_meet : ∀ (a d e x y : Point) (AB AC L M : Line),
  distinctPointsOnLine a d AB ∧ distinctPointsOnLine a e AC ∧ AB ≠ AC ∧
  distinctPointsOnLine d x L ∧ distinctPointsOnLine e y M ∧ ¬(x.onLine AB) ∧
  ¬(y.onLine AC) ∧ ∠ a:d:x = ∟ ∧ ∠ a:e:y = ∟ →
  ∃ f : Point, f.onLine L ∧ f.onLine M :=
by
  euclid_intros
  by_cases (L = M)
  · use d
    euclid_finish
  · by_cases (L.intersectsLine M)
    · euclid_apply (intersection_lines L M) as f
      use f
    · exfalso
      have : AB.intersectsLine M := by
        by_contra
        euclid_apply (parallel_line_unique d M AB L)
        euclid_finish
      euclid_apply (intersection_lines AB M) as p
      euclid_assert p ≠ d
      euclid_apply (point_on_line_same_side AB M x) as q
      euclid_assert p ≠ q
      euclid_apply (Elements.Book1.proposition_29_interior x q d p L M AB)
      euclid_apply (right_angle_on_lines a d x p x AB L)
      euclid_assert p ≠ a
      euclid_assert p ≠ e
      euclid_apply (right_angle_on_lines d p q a e AB M)
      euclid_apply (right_angle_on_lines a e y a p AC M)
      euclid_apply (extend_point AC a e) as z
      euclid_apply (Elements.Book1.proposition_32 p a e z AB AC M)
      euclid_finish

/-- A quadrilateral whose diagonals `ac`, `bd` cut one another at `e` is convex. -/
theorem quadrilateral_of_diagonals : ∀ (a b c d e : Point) (AB BC CD DA AC : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine b c BC ∧
  distinctPointsOnLine c d CD ∧ distinctPointsOnLine d a DA ∧
  distinctPointsOnLine a c AC ∧
  ¬(b.onLine AC) ∧ between a e c ∧ between b e d →
  quadrilateral a b c d AB BC CD DA :=
by
  euclid_intros
  euclid_finish

/-- The opposite sides of a square are parallel, the angles at the ends of each side being
right [Prop. 1.27]. -/
theorem square_parallel : ∀ (a b c d : Point) (AB BC CD DA : Line),
  square a b c d AB BC CD DA → ¬(AB.intersectsLine CD) ∧ ¬(BC.intersectsLine DA) :=
by
  euclid_intros
  euclid_apply (extend_point AB a b) as a'
  euclid_apply (extend_point BC b c) as b'
  euclid_apply (right_angle_on_lines a b c a' c AB BC)
  euclid_apply (right_angle_on_lines b c d b' d BC CD)
  euclid_apply (Elements.Book1.proposition_27 a' d b c AB CD BC)
  euclid_apply (Elements.Book1.proposition_27 b' a c d BC DA CD)
  euclid_finish

/-- A quadrilateral `abcd` in a circle, with `b`, `d` on either side of `ac`, is convex:
its diagonals cut one another within the circle. -/
theorem quadrilateral_of_circle : ∀ (a b c d : Point) (AB BC CD DA AC : Line)
    (α : Circle),
  a.onCircle α ∧ b.onCircle α ∧ c.onCircle α ∧ d.onCircle α ∧
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine b c BC ∧
  distinctPointsOnLine c d CD ∧ distinctPointsOnLine d a DA ∧
  distinctPointsOnLine a c AC ∧ b.opposingSides d AC →
  quadrilateral a b c d AB BC CD DA :=
by
  euclid_intros
  euclid_apply (line_from_points b d) as BD
  euclid_apply (intersection_lines_opposing b d AC BD)
  euclid_apply (intersection_lines AC BD) as p
  euclid_apply (circle_points_between b d p α)
  euclid_apply (circle_line_intersections p a c AC α)
  euclid_apply (quadrilateral_of_diagonals a b c d p AB BC CD DA AC)
  euclid_finish

/--
A pentagon `abcde` in a circle, with `b` across `ac` from `d`, and `e` across `ad` from
`c`, is convex: each four of its vertices make a convex quadrilateral.
-/
theorem pentagon_of_circle : ∀ (a b c d e : Point) (AB BC CD DE EA AC AD : Line)
    (α : Circle),
  a.onCircle α ∧ b.onCircle α ∧ c.onCircle α ∧ d.onCircle α ∧ e.onCircle α ∧
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine b c BC ∧
  distinctPointsOnLine c d CD ∧ distinctPointsOnLine d e DE ∧
  distinctPointsOnLine e a EA ∧ distinctPointsOnLine a c AC ∧
  distinctPointsOnLine a d AD ∧ b.opposingSides d AC ∧ e.opposingSides c AD →
  pentagon a b c d e AB BC CD DE EA :=
by
  euclid_intros
  euclid_apply (line_from_points b d) as BD
  euclid_apply (quadrilateral_of_circle a b c d AB BC CD AD AC α)
  euclid_apply (line_from_points b e) as BE
  euclid_apply (line_from_points c e) as CE
  euclid_apply (quadrilateral_of_circle a c d e AC CD DE EA AD α)
  euclid_apply (quadrilateral_of_circle a b c e AB BC CE EA AC α)
  euclid_apply (quadrilateral_of_circle a b d e AB BD DE EA AD α)
  euclid_apply (quadrilateral_of_circle b c d e BC CD DE BE BD α)
  euclid_finish

/-- An angle `bxc` in a circle less than a right angle has the center on its side of
`bc` [Props. 3.31, 3.31'']. -/
theorem centre_same_side_of_acute : ∀ (b c k x : Point) (BC : Line) (α : Circle),
  k.isCentre α ∧ b.onCircle α ∧ c.onCircle α ∧ x.onCircle α ∧
  distinctPointsOnLine b c BC ∧
  ¬(x.onLine BC) ∧ ∠ b:x:c < ∟ → k.sameSide x BC :=
by
  euclid_intros
  by_cases (k.onLine BC)
  · exfalso
    euclid_apply (Elements.Book3.proposition_31 x b c k BC α)
    euclid_finish
  · by_cases (k.sameSide x BC)
    · assumption
    · exfalso
      euclid_apply (Elements.Book3.proposition_31'' b c x k BC α)
      euclid_finish

/-- A line `CX` within an angle `ACD` in a circle meets the circle again at `E`, across
`AD` from `C`. -/
theorem ray_meets_circle : ∀ (a c d x : Point) (AC CD AD : Line) (α : Circle),
  a.onCircle α ∧ c.onCircle α ∧ d.onCircle α ∧ distinctPointsOnLine a c AC ∧
  distinctPointsOnLine c d CD ∧ distinctPointsOnLine a d AD ∧ x.sameSide d AC ∧
  x.sameSide a CD →
  ∃ e : Point, e.onCircle α ∧ e.opposingSides c AD ∧ ∠ a:c:e = ∠ a:c:x ∧
  ∠ d:c:e = ∠ d:c:x :=
by
  euclid_intros
  euclid_apply (line_from_points c x) as CX
  euclid_apply (intersection_lines_opposing a d CX AD)
  euclid_apply (intersection_lines CX AD) as p
  euclid_apply (circle_points_between a d p α)
  euclid_apply (intersection_circle_line_extending_points α CX p c) as e
  euclid_apply (equal_angles c x e a a CX AC)
  euclid_apply (equal_angles c x e d d CX CD)
  use e
  euclid_finish

/-- The perpendicular from `d` falls between `a` and `b` when the angles at both are less
than right angles [Prop. 1.12]. -/
theorem foot_between : ∀ (a b d : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ ¬(d.onLine AB) ∧ ∠ a:b:d < ∟ ∧ ∠ b:a:d < ∟ →
  ∃ e : Point, between a e b ∧ ∠ a:e:d = ∟ ∧ ∠ b:e:d = ∟ :=
by
  euclid_intros
  euclid_apply (perpendicular_foot a b d AB) as e
  have : e ≠ a := by
    intro
    euclid_finish
  euclid_apply (right_angle_move b e d a AB)
  euclid_apply (foot_on_ray b a d e AB)
  euclid_apply (between_points a e b AB)
  use e
  rcases ‹between a e b ∨ between e a b ∨ between a b e› with h | h | h
  · euclid_finish
  · exfalso
    euclid_finish
  · exfalso
    euclid_apply (between_symm a b e)
    euclid_finish

end Elements.Book4
