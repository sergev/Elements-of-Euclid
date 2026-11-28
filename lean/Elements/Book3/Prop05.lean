import SystemE

namespace Elements.Book3

/-- Two circles that cut one another do not have the same center. -/
theorem proposition_5 : ∀ (e : Point) (α β : Circle),
  α ≠ β ∧ α.intersectsCircle β ∧ e.isCentre α → ¬(e.isCentre β) :=
by
  euclid_intros
  -- if possible, let E be the center of both; join EC, and draw EFG at random
  euclid_apply (intersection_circles α β) as c
  euclid_apply (distinct_points e) as x
  euclid_apply (line_from_points e x) as EG
  euclid_apply (intersection_circle_line_extending_points α EG e x) as f
  euclid_apply (intersection_circle_line_extending_points β EG e x) as g
  -- EC = EF and EC = EG, so EF = EG
  euclid_apply (point_on_circle_onlyif e c f α)
  euclid_apply (point_on_circle_onlyif e c g β)
  -- Missed by Euclid: F ≠ G is read off the figure. With EF = EG the circles have one
  -- center and one radius, so they are the same circle.
  euclid_apply (equal_circles e f g α β)
  euclid_finish

end Elements.Book3
