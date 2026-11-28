import SystemE
import Elements.Book1.Prop09
import Elements.Book1.Prop26
import Elements.Book1.Prop32
import Elements.Book4.Lemmas

namespace Elements.Book4

/-- Perpendiculars `DE`, `DF` on the sides of an angle at `B` bisected by `BD` are equal
[Prop. 1.26]. -/
theorem proposition_4_equal : ∀ (a b c d e f : Point) (AB BC : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine b c BC ∧ ¬(d.onLine AB) ∧
  ¬(d.onLine BC) ∧ ∠ a:b:d = ∠ c:b:d ∧ e.onLine AB ∧ e ≠ b ∧ ¬(between e b a) ∧
  f.onLine BC ∧ f ≠ b ∧ ¬(between f b c) ∧ ∠ b:e:d = ∟ ∧ ∠ b:f:d = ∟ →
  |(d─e)| = |(d─f)| :=
by
  euclid_intros
  euclid_apply (line_from_points e d) as ED
  euclid_apply (line_from_points f d) as FD
  euclid_apply (line_from_points b d) as BD
  euclid_apply (equal_angles b a e d d AB BD)
  euclid_apply (equal_angles b c f d d BC BD)
  euclid_apply (Elements.Book1.proposition_26 d b e d b f BD AB ED BD BC FD)
  euclid_finish

/--
The center `D` within the triangle, on the bisectors of the angles at `B` and `C`: the
perpendiculars `DE`, `DF`, `DG` fall on the sides, and the circle with center `D` and
radius `DE` touches them there.
-/
theorem proposition_4_lemma : ∀ (a b c d : Point) (AB BC CA : Line),
  formTriangle a b c AB BC CA ∧ d.sameSide c AB ∧ d.sameSide b CA ∧ d.sameSide a BC ∧
  ∠ a:b:d = ∠ c:b:d ∧ ∠ a:c:d = ∠ b:c:d ∧ ∠ a:b:d < ∟ ∧ ∠ a:c:d < ∟ →
  ∃ (e f g : Point) (α : Circle), d.isCentre α ∧
  circumscribedTriangle a b c AB BC CA e f g α :=
by
  euclid_intros
  -- DE, DF, DG drawn perpendicular to AB, BC, CA [Prop. 1.12]. Missed by Euclid: they
  -- fall on the sides, the halves of the angles being less than right angles.
  euclid_apply (perpendicular_foot a b d AB) as e
  euclid_apply (perpendicular_foot c b d BC) as f
  euclid_apply (perpendicular_foot a c d CA) as g
  euclid_apply (right_angle_move b f d c BC)
  euclid_apply (foot_on_ray b c d f BC)
  -- EBD and FBD have two angles equal and BD common: DE = DF [Prop. 1.26]; and
  -- similarly DG = DF
  euclid_apply (proposition_4_equal a b c d e f AB BC)
  euclid_apply (proposition_4_equal a c b d g f CA BC)
  -- the circle with center D and radius DE goes through F and G, and touches AB, BC,
  -- CA, the angles at E, F, G being right [Prop. 3.16 corollary]
  euclid_apply (circle_from_points d e) as α
  euclid_apply (point_on_circle_if d e f α)
  euclid_apply (point_on_circle_if d e g α)
  euclid_apply (touches_of_perpendicular d e b AB α)
  euclid_apply (touches_of_perpendicular d f b BC α)
  euclid_apply (touches_of_perpendicular d g c CA α)
  -- Missed by Euclid: E, F, G are between the vertices, being on the circle's side,
  -- and the center's, of the other sides. E and G are not both at A, where the right
  -- angles would make a straight line BAC.
  have : e ≠ g := by
    intro
    euclid_apply (sum_angles_onlyif a b c d AB CA)
    euclid_apply (flat_angle_if b a c)
    euclid_finish
  euclid_apply (centre_same_side_of_touches g e d CA α)
  euclid_apply (centre_same_side_of_touches f e d BC α)
  euclid_apply (centre_same_side_of_touches e f d AB α)
  euclid_apply (centre_same_side_of_touches g f d CA α)
  euclid_apply (centre_same_side_of_touches e g d AB α)
  euclid_apply (centre_same_side_of_touches f g d BC α)
  euclid_apply (between_of_same_sides a b e AB CA BC)
  euclid_apply (between_of_same_sides b c f BC AB CA)
  euclid_apply (between_of_same_sides c a g CA BC AB)
  use e, f, g, α

/-- To inscribe a circle `α`, with center `d`, in a given triangle `ABC`; it touches `AB`,
`BC`, `CA` at `E`, `F`, `G`. -/
theorem proposition_4 : ∀ (a b c : Point) (AB BC CA : Line),
  formTriangle a b c AB BC CA →
  ∃ (d e f g : Point) (α : Circle), d.isCentre α ∧
  circumscribedTriangle a b c AB BC CA e f g α :=
by
  euclid_intros
  -- let the angles ABC, ACB be cut in half by BD, CD [Prop. 1.9]
  euclid_apply (Elements.Book1.proposition_9 b a c AB BC) as x
  euclid_apply (Elements.Book1.proposition_9 c a b CA BC) as y
  euclid_apply (line_from_points b x) as BD
  euclid_apply (line_from_points c y) as CD
  -- Missed by Euclid: they meet, within the triangle, since the halves of ABC and ACB
  -- are together less than two right angles [Prop. 1.32].
  euclid_apply (sum_angles_onlyif b a c x AB BC)
  euclid_apply (sum_angles_onlyif c a b y CA BC)
  euclid_apply (extend_point BC b c) as z
  euclid_apply (Elements.Book1.proposition_32 a b c z AB BC CA)
  euclid_apply (lines_intersect x b c y BD BC CD) as d
  euclid_assert d.sameSide c AB
  euclid_assert d.sameSide b CA
  euclid_assert d.sameSide a BC
  euclid_apply (equal_angles b x d a a BD AB)
  euclid_apply (equal_angles b x d c c BD BC)
  euclid_apply (equal_angles c y d a a CD CA)
  euclid_apply (equal_angles c y d b b CD BC)
  euclid_apply (proposition_4_lemma a b c d AB BC CA) as (e, f, g, α)
  use d, e, f, g, α

end Elements.Book4
