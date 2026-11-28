import SystemE
import Elements.Book1.Prop05
import Elements.Book1.Prop10
import Elements.Book1.Prop11
import Elements.Book1.Prop12
import Elements.Book1.Prop13
import Elements.Book1.Prop29
import Elements.Book1.Prop32
import Elements.Book3.Prop16
import Elements.Book3.Prop18

/-
Facts Book 4 takes from the figure.
-/

namespace Elements.Book4

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

end Elements.Book4
