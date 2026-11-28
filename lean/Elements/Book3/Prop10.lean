import SystemE
import Elements.Book3.Prop05
import Elements.Book3.Prop09

namespace Elements.Book3

/-- A circle does not cut another circle at more than two points. -/
theorem proposition_10 : ∀ (b g h p q : Point) (α β : Circle),
  α ≠ β ∧ α.intersectsCircle β ∧ b.onCircle α ∧ g.onCircle α ∧ h.onCircle α ∧
  b.onCircle β ∧ g.onCircle β ∧ h.onCircle β ∧ b ≠ g ∧ g ≠ h ∧ h ≠ b ∧
  p.isCentre α ∧ q.isCentre β → False :=
by
  euclid_intros
  -- the perpendiculars bisecting BH and BG meet at the center P of α; so, similarly,
  -- P is the center of β [Props. 3.1 corollary, 3.9]
  euclid_apply (point_on_circle_onlyif p b g α)
  euclid_apply (point_on_circle_onlyif p g h α)
  euclid_apply (proposition_9' b g h p q β)
  -- two circles cutting one another have the same center P [Prop. 3.5]
  euclid_apply (proposition_5 p α β)
  euclid_finish

end Elements.Book3
