import SystemE
import Elements.Book1.Prop10
import Elements.Book1.Prop11
import Elements.Book1.Prop16
import Elements.Book3.Prop09
import Elements.Book3.Prop21

namespace Elements.Book3

/--
Euclid's argument in Prop. 3.23: segments of `α` and `β` on `AB`, on one side, with a
point `C` of `α` inside `β`. Then `AC` produced meets `β` at `D`, and the angle `ACB` is
greater than `ADB` [Prop. 1.16]; they cannot admit equal angles.
-/
theorem proposition_23_lemma : ∀ (a b c y o : Point) (AB : Line) (α β : Circle),
  distinctPointsOnLine a b AB ∧ a.onCircle α ∧ b.onCircle α ∧ a.onCircle β ∧
  b.onCircle β ∧ c.onCircle α ∧ c.insideCircle β ∧ c.sameSide y AB ∧ y.onCircle β ∧
  o.isCentre β ∧ ∠ a:c:b = ∠ a:y:b → False :=
by
  euclid_intros
  -- let ACD be drawn through the segments, and CB, DB joined
  euclid_apply (line_from_points a c) as AC
  euclid_apply (intersection_circle_line_extending_points β AC c a) as d
  euclid_apply (line_from_points b c) as BC
  euclid_apply (line_from_points b d) as BD
  -- ADB is equal to the angle in the segment of β [Prop. 3.21]
  euclid_apply (proposition_21 d a b y o AB β)
  -- the external angle ACB is greater than the internal ADB [Prop. 1.16]
  euclid_apply (Elements.Book1.proposition_16 b d c a BD AC BC)
  euclid_apply (equal_angles d a c b b AC BD)
  euclid_finish

/-- Two similar and unequal segments cannot be constructed on one side of a line `AB`. -/
theorem proposition_23 : ∀ (a b x y o₁ o₂ : Point) (AB : Line) (α β : Circle),
  similarSegments α a b AB x β a b AB y ∧ x.sameSide y AB ∧
  o₁.isCentre α ∧ o₂.isCentre β →
  α = β :=
by
  euclid_intros
  -- Missed by Euclid: a line through the segments, the perpendicular bisecting AB at M,
  -- meets them at C and D [Props. 1.10, 1.11].
  euclid_apply (Elements.Book1.proposition_10 a b AB) as m
  euclid_apply (Elements.Book1.proposition_11' a b m x AB) as p
  euclid_apply (line_from_points m p) as MP
  euclid_apply (extend_point MP p m) as q
  euclid_apply (circle_points_between a b m α)
  euclid_apply (circle_points_between a b m β)
  euclid_apply (intersection_circle_line_extending_points α MP m q) as c
  euclid_apply (intersection_circle_line_extending_points β MP m q) as d
  -- the angles in the segments are those at C and D [Prop. 3.21]
  euclid_apply (proposition_21 c a b x o₁ AB α)
  euclid_apply (proposition_21 d a b y o₂ AB β)
  by_cases (c = d)
  · -- three points in common: the circles are one [Prop. 3.9]
    euclid_apply (point_on_circle_onlyif o₂ a b β)
    euclid_apply (point_on_circle_onlyif o₂ a c β)
    euclid_apply (proposition_9' a b c o₂ o₁ α)
    euclid_apply (centre_unique o₁ o₂ α)
    euclid_apply (equal_circles o₁ a a α β)
    euclid_finish
  · exfalso
    -- one of C, D is nearer to M, and inside the other circle
    euclid_apply (between_points m c d MP)
    rcases ‹_ ∨ _ ∨ _› with _ | _ | _
    · euclid_apply (circle_points_between m d c β)
      euclid_apply (proposition_23_lemma a b c y o₂ AB α β)
      euclid_finish
    · euclid_apply (not_between_of_between_1 c m q)
      euclid_finish
    · euclid_apply (circle_points_between m c d α)
      euclid_apply (proposition_23_lemma a b d x o₁ AB β α)
      euclid_finish

end Elements.Book3
