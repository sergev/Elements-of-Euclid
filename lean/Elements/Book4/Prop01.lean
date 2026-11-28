import SystemE
import Elements.Book1.Prop03

namespace Elements.Book4

/--
To insert into a circle `α`, with center `o`, a straight line equal to a given one `D`
(from `d₀` to `d₁`), not greater than the diameter. It is inserted from `C`, the end of
the diameter `BC`, which may be any point of the circle.
-/
theorem proposition_1 : ∀ (o c d₀ d₁ : Point) (α : Circle),
  o.isCentre α ∧ c.onCircle α ∧ d₀ ≠ d₁ ∧ |(d₀─d₁)| ≤ |(o─c)| + |(o─c)| →
  ∃ a : Point, insertedInto c a α ∧ |(c─a)| = |(d₀─d₁)| :=
by
  euclid_intros
  -- let a diameter BC be drawn
  euclid_apply (line_from_points o c) as BC
  euclid_apply (intersection_circle_line_extending_points α BC o c) as b
  euclid_apply (between_if b o c)
  euclid_apply (point_on_circle_onlyif o c b α)
  by_cases (|(b─c)| = |(d₀─d₁)|)
  · -- BC, equal to D, is inserted into the circle
    use b
    euclid_finish
  · -- BC is greater than D: let CE be made equal to D [Prop. 1.3]
    euclid_apply (line_from_points d₀ d₁) as D
    euclid_apply (Elements.Book1.proposition_3 c b d₀ d₁ BC D) as e
    -- the circle EAF, with center C and radius CE, meets the circle at A
    euclid_apply (circle_from_points c e) as EAF
    euclid_apply (circle_points_between b c e α)
    euclid_apply (intersection_circle_circle_2 c e α EAF)
    euclid_apply (intersection_circles α EAF) as a
    -- CA = CE, and CE = D: CA = D
    euclid_apply (point_on_circle_onlyif c e a EAF)
    use a
    euclid_finish

end Elements.Book4
