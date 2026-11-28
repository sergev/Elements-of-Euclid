import SystemE
import Elements.Book1.Prop04
import Elements.Book1.Prop10
import Elements.Book1.Prop11
import Elements.Book4.Lemmas

namespace Elements.Book4

/-- A point `F` of the line `DX` at right angles to `AB` at its midpoint `D` is equally
distant from `A` and `B`: `AD = DB`, `DF` common and at right angles [Prop. 1.4]. -/
theorem proposition_5_equal : ∀ (a b d f x : Point) (AB DX : Line),
  distinctPointsOnLine a b AB ∧ between a d b ∧ |(a─d)| = |(d─b)| ∧
  distinctPointsOnLine d x DX ∧ ¬(x.onLine AB) ∧ ∠ a:d:x = ∟ ∧ f.onLine DX →
  |(f─a)| = |(f─b)| :=
by
  euclid_intros
  by_cases (f = d)
  · euclid_finish
  · euclid_apply (line_from_points f a) as FA
    euclid_apply (line_from_points f b) as FB
    euclid_apply (right_angle_on_lines a d x a f AB DX)
    euclid_apply (right_angle_on_lines a d x b f AB DX)
    euclid_apply (Elements.Book1.proposition_4 d a f d b f AB FA DX AB FB DX)
    euclid_finish

/-- Euclid's argument, the same in each figure: `FA = FB` and `FA = FC`, and the circle
with center `F` and radius `FA` goes through `B` and `C`. -/
theorem proposition_5_lemma : ∀ (a b c d e f x y : Point) (AB CA DX EY : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine a c CA ∧ between a d b ∧
  |(a─d)| = |(d─b)| ∧ between a e c ∧ |(a─e)| = |(e─c)| ∧ distinctPointsOnLine d x DX ∧
  ¬(x.onLine AB) ∧ ∠ a:d:x = ∟ ∧ distinctPointsOnLine e y EY ∧ ¬(y.onLine CA) ∧
  ∠ a:e:y = ∟ ∧ f.onLine DX ∧ f.onLine EY →
  ∃ α : Circle, f.isCentre α ∧ inscribedTriangle a b c α :=
by
  euclid_intros
  euclid_apply (proposition_5_equal a b d f x AB DX)
  euclid_apply (proposition_5_equal a c e f y CA EY)
  -- Missed by Euclid: F is not A, being on DX, off AB.
  have : f ≠ a := by
    intro
    euclid_apply (right_angle_on_lines a d x a f AB DX)
    euclid_finish
  euclid_apply (circle_from_points f a) as α
  euclid_apply (point_on_circle_if f a b α)
  euclid_apply (point_on_circle_if f a c α)
  use α

/-- To circumscribe a circle `α`, with center `F`, about a given triangle `ABC`. -/
theorem proposition_5 : ∀ (a b c : Point) (AB BC CA : Line),
  formTriangle a b c AB BC CA →
  ∃ (f : Point) (α : Circle), f.isCentre α ∧ inscribedTriangle a b c α :=
by
  euclid_intros
  -- AB, AC cut in half at D, E [Prop. 1.10]; DF, EF at right angles to them [Prop. 1.11]
  euclid_apply (Elements.Book1.proposition_10 a b AB) as d
  euclid_apply (Elements.Book1.proposition_10 a c CA) as e
  euclid_apply (Elements.Book1.proposition_11 a b d AB) as x
  euclid_apply (Elements.Book1.proposition_11 a c e CA) as y
  euclid_apply (line_from_points d x) as DX
  euclid_apply (line_from_points e y) as EY
  -- Missed by Euclid: they meet, at F.
  euclid_apply (perpendiculars_meet a d e x y AB CA DX EY) as f
  -- They meet inside the triangle (on A's side of BC), on BC, or beyond BC.
  by_cases (f.sameSide a BC)
  · -- inside: join FB, FC, FA
    euclid_apply (proposition_5_lemma a b c d e f x y AB CA DX EY) as α
    use f, α
  · by_cases (f.onLine BC)
    · -- on BC: join AF
      euclid_apply (proposition_5_lemma a b c d e f x y AB CA DX EY) as α
      use f, α
    · -- beyond BC: join AF, BF, CF
      euclid_apply (proposition_5_lemma a b c d e f x y AB CA DX EY) as α
      use f, α

end Elements.Book4
