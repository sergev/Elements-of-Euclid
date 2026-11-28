import SystemE
import Elements.Book1.Prop08
import Elements.Book1.Prop20
import Elements.Book1.Prop22

namespace Elements.Book1

-- Prop. 23 for an angle whose sides are on different lines, on the side of AB where x is.
theorem proposition_23_side : ∀ (a b c d e x : Point) (AB CD CE : Line),
  distinctPointsOnLine a b AB ∧ formRectilinearAngle d c e CD CE ∧ ¬(d.onLine CE) ∧ ¬(x.onLine AB) →
  ∃ f : Point, f.sameSide x AB ∧ (∠ f:a:b = ∠ d:c:e) :=
by
  euclid_intros
  euclid_apply (line_from_points d e) as DE
  -- Euclid didn't explicitly apply proposition_20.
  euclid_apply (proposition_20 c d e CD DE CE)
  euclid_apply (proposition_20 d e c DE CE CD)
  euclid_apply (proposition_20 e c d CE CD DE)
  euclid_apply (proposition_22_side c d c e e d a b x CD CE DE AB) as (f, g)
  euclid_apply (line_from_points a f) as AF
  euclid_apply (line_from_points f g) as FG
  euclid_apply (proposition_8 c d e a f g CD DE CE AF FG AB)
  euclid_apply (equal_angles a f f b g AF AB)
  refine ⟨f, ?_, ?_⟩ <;> euclid_finish

-- An extension of proposition_23 that allows the angle to be constructed on either side of AB.
theorem proposition_23' : ∀ (a b c d e x : Point) (AB CD CE : Line),
  distinctPointsOnLine a b AB ∧ formRectilinearAngle d c e CD CE ∧ ¬(x.onLine AB) →
  ∃ f : Point, f ≠ a ∧ (f.onLine AB ∨ f.sameSide x AB) ∧ (∠ f:a:b = ∠ d:c:e) :=
by
  euclid_intros
  by_cases (d.onLine CE)
  · -- Omitted by Euclid.
    by_cases (∠ d:c:e = 0)
    · euclid_apply (degenerated_angle_if a b b AB)
      refine ⟨b, ?_, Or.inl ?_, ?_⟩ <;> euclid_finish
    · have : between d c e := by
        by_contra
        euclid_apply (degenerated_angle_if c d e CE)
        euclid_finish
      euclid_apply (flat_angle_onlyif d c e)
      euclid_apply (extend_point AB b a) as b'
      euclid_apply (flat_angle_onlyif b' a b)
      refine ⟨b', ?_, Or.inl ?_, ?_⟩ <;> euclid_finish
  euclid_apply (proposition_23_side a b c d e x AB CD CE) as f
  refine ⟨f, ?_, Or.inr ?_, ?_⟩ <;> euclid_finish

-- A right angle is not nothing: some angle is positive [Prop. 1.1], and none exceeds two right angles.
theorem right_angle_pos : (0 : ℝ) < ∟ := by
  euclid_apply arbitrary_point as a
  euclid_apply (distinct_points a) as b
  euclid_apply (line_from_points a b) as AB
  euclid_apply (proposition_1 a b AB) as c
  have h1 := angle_pos_of_not_on_line a b c AB (by euclid_finish)
  have h2 := (angle_range (Angle.ofPoints b a c)).2
  linarith

-- An angle of neither nothing nor two right angles has its sides on different lines.
theorem not_on_line_of_angle : ∀ (d c e : Point) (CD CE : Line),
  formRectilinearAngle d c e CD CE ∧ 0 < (∠ d:c:e : ℝ) ∧ (∠ d:c:e : ℝ) < ∟ + ∟ → ¬(d.onLine CE) :=
by
  euclid_intros
  by_cases (between d c e)
  · euclid_apply (flat_angle_onlyif d c e)
    euclid_finish
  · euclid_apply (degenerated_angle_if c d e CE)
    euclid_finish

theorem proposition_23 : ∀ (a b c d e : Point) (AB CD CE : Line),
  distinctPointsOnLine a b AB ∧ formRectilinearAngle d c e CD CE →
  ∃ f : Point, f ≠ a ∧ (∠ f:a:b = ∠ d:c:e) :=
by
  euclid_intros
  euclid_apply (proposition_1 a b AB) as x
  euclid_apply (proposition_23' a b c d e x AB CD CE) as f
  use f

end Elements.Book1
