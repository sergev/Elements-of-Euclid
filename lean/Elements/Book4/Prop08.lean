import SystemE
import Elements.Book1.Prop10
import Elements.Book1.Prop29
import Elements.Book1.Prop30
import Elements.Book1.Prop31
import Elements.Book1.Prop34
import Elements.Book2.Lemmas
import Elements.Book4.Lemmas

namespace Elements.Book4

/-- To inscribe a circle `α`, with center `g`, in a given square `ABCD`; it touches `AB`,
`BC`, `CD`, `DA` at `F`, `H`, `K`, `E`. -/
theorem proposition_8 : ∀ (a b c d : Point) (AB BC CD DA : Line),
  square a b c d AB BC CD DA →
  ∃ (g f h k e : Point) (α : Circle), g.isCentre α ∧
  circumscribedQuadrilateral a b c d AB BC CD DA f h k e α :=
by
  euclid_intros
  euclid_apply (square_parallel a b c d AB BC CD DA)
  -- AD, AB cut in half at E, F [Prop. 1.10]; EH through E parallel to AB, and FK
  -- through F parallel to AD [Prop. 1.31]
  euclid_apply (Elements.Book1.proposition_10 a d DA) as e
  euclid_apply (Elements.Book1.proposition_10 a b AB) as f
  euclid_apply (Elements.Book1.proposition_31 e a b AB) as EH
  euclid_apply (Elements.Book1.proposition_31 f a d DA) as FK
  -- Missed by Euclid: EH meets BC at H and FK, at G; FK meets CD at K. They are
  -- parallel to CD and BC [Prop. 1.30], and the points fall in order.
  euclid_apply (Elements.Book1.proposition_30 EH CD AB)
  euclid_apply (Elements.Book1.proposition_30 FK BC DA)
  have : EH.intersectsLine BC := by
    by_contra
    euclid_apply (parallel_line_unique b EH AB BC)
    euclid_finish
  have : FK.intersectsLine CD := by
    by_contra
    euclid_apply (parallel_line_unique d FK DA CD)
    euclid_finish
  have : EH.intersectsLine FK := by
    by_contra
    euclid_apply (parallel_line_unique f EH AB FK)
    euclid_finish
  euclid_apply (intersection_lines EH BC) as h
  euclid_apply (intersection_lines FK CD) as k
  euclid_apply (intersection_lines EH FK) as g
  euclid_apply (Elements.Book2.parallel_between a e d b h c AB EH CD BC)
  euclid_apply (Elements.Book2.parallel_between a f b d k c DA FK BC CD)
  euclid_apply (Elements.Book2.parallel_between a f b e g h DA FK BC EH)
  euclid_apply (Elements.Book2.parallel_between a e d f g k AB EH CD FK)
  -- AG, BG, GD are parallelograms, with opposite sides equal [Prop. 1.34]; AE = AF,
  -- halves of equal sides: GE, GF, GH, GK are equal
  euclid_apply (Elements.Book1.proposition_34' a f e g AB EH DA FK)
  euclid_apply (Elements.Book1.proposition_34' f b g h AB EH FK BC)
  euclid_apply (Elements.Book1.proposition_34' e g d k EH CD DA FK)
  euclid_apply (between_if a e d)
  euclid_apply (between_if a f b)
  -- the angles at E, F, H, K are right [Prop. 1.29]
  euclid_apply (equal_angles a d e b f DA AB)
  euclid_apply (equal_angles b a f c h AB BC)
  euclid_apply (equal_angles d a e c k DA CD)
  euclid_apply (Elements.Book1.proposition_29_interior e g a f DA FK AB)
  euclid_apply (Elements.Book1.proposition_29_interior f g a e AB EH DA)
  euclid_apply (Elements.Book1.proposition_29_interior f g b h AB EH BC)
  euclid_apply (Elements.Book1.proposition_29_interior e g d k DA FK CD)
  -- the circle with center G and radius GE goes through F, H, K, and touches the sides,
  -- the angles at E, F, H, K being right [Prop. 3.16 corollary]
  euclid_apply (circle_from_points g e) as α
  euclid_apply (point_on_circle_if g e f α)
  euclid_apply (point_on_circle_if g e h α)
  euclid_apply (point_on_circle_if g e k α)
  euclid_apply (touches_of_perpendicular g f a AB α)
  euclid_apply (touches_of_perpendicular g e a DA α)
  euclid_apply (touches_of_perpendicular g h b BC α)
  euclid_apply (touches_of_perpendicular g k d CD α)
  use g, f, h, k, e, α
  euclid_finish

end Elements.Book4
