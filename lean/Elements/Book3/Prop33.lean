import SystemE
import Elements.Book1.Prop04
import Elements.Book1.Prop10
import Elements.Book1.Prop11
import Elements.Book1.Prop23
import Elements.Book1.Prop29
import Elements.Book3.Prop16
import Elements.Book3.Prop32

namespace Elements.Book3

/--
On a given straight line `AB`, to draw a segment of a circle admitting an angle equal to a
given rectilinear angle `C₁CC₂`: a circle `α` through `A`, `B`, and `X` on it, off `AB`.
-/
theorem proposition_33 : ∀ (a b c c₁ c₂ : Point) (AB CC₁ CC₂ : Line),
  distinctPointsOnLine a b AB ∧ formRectilinearAngle c₁ c c₂ CC₁ CC₂ ∧ ¬(c₁.onLine CC₂) →
  ∃ (α : Circle) (x : Point), a.onCircle α ∧ b.onCircle α ∧ x.onCircle α ∧
  ¬(x.onLine AB) ∧ ∠ a:x:b = ∠ c₁:c:c₂ :=
by
  euclid_intros
  -- the angle BAD equal to C [Prop. 1.23]
  euclid_apply (Elements.Book1.proposition_11_end a b AB) as x₀
  euclid_apply (Elements.Book1.proposition_23_side a b c c₁ c₂ x₀ AB CC₁ CC₂) as d
  euclid_apply (line_from_points a d) as AD
  -- AE at right angles to AD [Prop. 1.11]; AB cut in half at F [Prop. 1.10], and FG at
  -- right angles to AB [Prop. 1.11]
  euclid_apply (Elements.Book1.proposition_11_end a d AD) as e
  euclid_apply (line_from_points a e) as AE
  euclid_apply (Elements.Book1.proposition_10 a b AB) as f
  euclid_apply (Elements.Book1.proposition_11 a b f AB) as g'
  euclid_apply (line_from_points f g') as FG
  -- Missed by Euclid: AE meets FG at G; were they parallel, AE would be at right angles
  -- to AB too, and AD would be AB. (When C is right, G is F; Euclid treats it apart.)
  have : AE.intersectsLine FG := by
    by_contra
    euclid_assert ¬(e.onLine AB)
    have : ∃ a' : Point, a'.onLine AE ∧ a' ≠ a ∧ a'.opposingSides g' AB := by
      by_cases (e.sameSide g' AB)
      · euclid_apply (extend_point AE e a) as a'
        use a'
        euclid_finish
      · use e
        euclid_finish
    obtain ⟨a', _, _, _⟩ := this
    euclid_apply (Elements.Book1.proposition_29_alternate a' g' a f AE FG AB)
    euclid_apply (right_angle_on_lines a f g' a g' AB FG)
    euclid_apply (equal_angles a f b a' a' AB AE)
    euclid_apply (right_angle_on_lines e a d a' d AE AD)
    by_cases (d.sameSide b AE)
    · euclid_apply (on_line_of_eq_angle d AB a b a' AE)
      euclid_finish
    · euclid_apply (extend_point AB b a) as b'
      euclid_apply (right_angle_on_lines a' a b a' b' AE AB)
      euclid_apply (on_line_of_eq_angle d AB a b' a' AE)
      euclid_finish
  euclid_apply (intersection_lines AE FG) as g
  -- AF = FB, FG common, and the angles at F right: AG = BG [Prop. 1.4]
  have : |(g─a)| = |(g─b)| := by
    by_cases (g = f)
    · euclid_finish
    · euclid_apply (line_from_points g b) as GB
      euclid_apply (right_angle_on_lines a f g' a g AB FG)
      euclid_apply (right_angle_on_lines a f g' b g AB FG)
      euclid_apply (Elements.Book1.proposition_4 f a g f b g AB AE FG AB GB FG)
      euclid_finish
  -- the circle with center G and radius GA goes through B
  euclid_apply (circle_from_points g a) as α
  euclid_apply (point_on_circle_if g a b α)
  -- AD is at right angles to the diameter AE, at its end: it touches the circle
  -- [Prop. 3.16 corollary]
  euclid_apply (intersection_circle_line_extending_points α AE g a) as e'
  euclid_apply (right_angle_on_lines e a d e' d AE AD)
  euclid_apply (proposition_16_corollary a e' g d AD α)
  -- DAB is equal to the angle in the alternate segment [Prop. 3.32]. Missed by Euclid:
  -- the circle has points P, Q on FG, one on either side of AB.
  euclid_apply (circle_points_between a b f α)
  euclid_apply (intersection_circle_line_extending_points α FG f g') as p
  euclid_apply (intersection_circle_line_extending_points α FG f p) as q
  euclid_apply (extend_point AD d a) as d'
  by_cases (p.sameSide d AB)
  · euclid_apply (proposition_32 a b d' d g q p AB AD α)
    use α, q
    euclid_finish
  · euclid_apply (proposition_32 a b d' d g p q AB AD α)
    use α, p
    euclid_finish

end Elements.Book3
