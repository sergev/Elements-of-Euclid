import SystemE
import Elements.Book1.Prop10
import Elements.Book1.Prop11
import Elements.Book1.Prop23
import Elements.Book3.Prop16
import Elements.Book3.Prop32

namespace Elements.Book3

/--
From a given circle (center `O`), to cut off a segment admitting an angle equal to a given
rectilinear angle `D₁DD₂`: the chord `BC`, and `X` in the segment.
-/
theorem proposition_34 : ∀ (d d₁ d₂ o : Point) (DD₁ DD₂ : Line) (α : Circle),
  o.isCentre α ∧ formRectilinearAngle d₁ d d₂ DD₁ DD₂ ∧ ¬(d₁.onLine DD₂) →
  ∃ (b c x : Point) (BC : Line), distinctPointsOnLine b c BC ∧ b.onCircle α ∧
  c.onCircle α ∧ x.onCircle α ∧ ¬(x.onLine BC) ∧ ∠ b:x:c = ∠ d₁:d:d₂ :=
by
  euclid_intros
  -- EF touching the circle at B: at right angles to the radius OB [Props. 3.1, 1.11,
  -- 3.16 corollary]
  euclid_apply (exists_point_on_circle α) as b
  euclid_apply (line_from_points o b) as OB
  euclid_apply (Elements.Book1.proposition_11_end b o OB) as f
  euclid_apply (line_from_points b f) as EF
  euclid_apply (intersection_circle_line_extending_points α OB o b) as b'
  euclid_apply (right_angle_on_lines o b f b' f OB EF)
  euclid_apply (proposition_16_corollary b b' o f EF α)
  -- the angle FBC equal to D [Prop. 1.23]; BC cuts the circle again at C [Prop. 3.16]
  euclid_apply (Elements.Book1.proposition_23_side b f d d₁ d₂ o EF DD₁ DD₂) as c'
  euclid_apply (line_from_points b c') as BC
  euclid_apply (proposition_16' b b' o f EF BC α)
  euclid_apply (intersections_circle_line α BC) as (p, q)
  have : ∃ c : Point, c.onCircle α ∧ c.onLine BC ∧ c ≠ b := by
    by_cases (p = b)
    · use q
      euclid_finish
    · use p
  obtain ⟨c, _, _, _⟩ := this
  euclid_apply (equal_angles b c' c f f BC EF)
  -- FBC is equal to the angle in the alternate segment BAC [Prop. 3.32]. Missed by
  -- Euclid: the segments on either side of BC have points X, Y.
  euclid_apply (Elements.Book1.proposition_10 b c BC) as m
  euclid_apply (circle_points_between b c m α)
  euclid_apply (line_from_points m f) as MF
  euclid_apply (intersection_circle_line_extending_points α MF m f) as x
  euclid_apply (intersection_circle_line_extending_points α MF m x) as y
  euclid_apply (extend_point EF f b) as e
  euclid_apply (proposition_32 b c e f o x y BC EF α)
  use b, c, x, BC
  euclid_finish

end Elements.Book3
