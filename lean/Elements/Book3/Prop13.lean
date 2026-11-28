import SystemE
import Elements.Book3.Prop02
import Elements.Book3.Prop11

namespace Elements.Book3

/-- A circle `β` touching `α` internally at `D` touches it at no other point `B`. -/
theorem proposition_13 : ∀ (b d g h : Point) (α β : Circle),
  β.touchesInternallyAt α d ∧ b.onCircle α ∧ b.onCircle β ∧ g.isCentre α ∧ h.isCentre β →
  b = d :=
by
  euclid_intros
  by_contra
  -- Missed by Euclid: G and H are distinct [Prop. 3.6].
  euclid_apply (proposition_6 d h β α)
  -- the line joining G and H falls on B and D [Prop. 3.11]
  euclid_apply (line_from_points g h) as GH
  euclid_apply (proposition_11 d g h GH α β)
  euclid_apply (proposition_11 b g h GH α β)
  -- BG = GD and BH = HD, with G and H both between B and D: G and H coincide
  euclid_apply (circle_line_intersections g b d GH α)
  euclid_apply (circle_line_intersections h b d GH β)
  euclid_apply (point_on_circle_onlyif g b d α)
  euclid_apply (point_on_circle_onlyif h b d β)
  euclid_apply (between_if b g d)
  euclid_apply (between_if b h d)
  euclid_apply (eq_of_same_ray g h b GH)
  euclid_finish

/-- Circles touching externally at `A` touch at no other point `C`. -/
theorem proposition_13' : ∀ (a c f g : Point) (α β : Circle),
  α.touchesExternallyAt β a ∧ c.onCircle α ∧ c.onCircle β ∧ f.isCentre α ∧ g.isCentre β →
  c = a :=
by
  euclid_intros
  by_contra
  -- join AC: it falls inside each circle [Prop. 3.2], but it fell outside one [Def. 3.3]
  euclid_apply (line_from_points a c) as AC
  euclid_apply (exists_point_between_points_on_line AC a c) as e
  euclid_apply (proposition_2 a c f e α)
  euclid_apply (proposition_2 a c g e β)
  euclid_apply (‹∀ x : Point, x.insideCircle α → ¬x.insideCircle β› e)
  euclid_finish

end Elements.Book3
