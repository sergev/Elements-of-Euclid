import SystemE
import Elements.Book1.Prop20
import Elements.Book3.Prop06

namespace Elements.Book3

/--
Circles touching internally at `A`, `β` within `α`: the line `FG` joining their centers,
produced, falls on `A`.
-/
theorem proposition_11 : ∀ (a f g : Point) (FG : Line) (α β : Circle),
  β.touchesInternallyAt α a ∧ f.isCentre α ∧ g.isCentre β ∧ f.onLine FG ∧ g.onLine FG →
  a.onLine FG :=
by
  euclid_intros
  -- Missed by Euclid: F and G are distinct [Prop. 3.6].
  euclid_apply (proposition_6 a g β α)
  -- G is inside α
  euclid_apply (‹∀ x : Point, x.insideCircle β → x.insideCircle α› g)
  by_contra
  -- if possible, let it fall like FGH, and let AF, AG be joined
  euclid_apply (intersection_circle_line_extending_points α FG g f) as h
  euclid_apply (intersection_circle_line_extending_points β FG g f) as d
  euclid_apply (line_from_points a f) as AF
  euclid_apply (line_from_points a g) as AG
  -- AG and GF are greater than FA, that is FH [Prop. 1.20]; take FG from both:
  -- AG, that is GD, is greater than GH
  euclid_apply (Elements.Book1.proposition_20 g a f AG AF FG)
  euclid_apply (point_on_circle_onlyif f a h α)
  euclid_apply (point_on_circle_onlyif g a d β)
  euclid_apply (between_if h g f)
  -- Missed by Euclid: then H is between G and D, inside β and so inside α; but H is on α.
  euclid_assert between g h d
  euclid_apply (‹∀ x : Point, x.insideCircle β → x.insideCircle α› h)
  euclid_finish

end Elements.Book3
