import SystemE

namespace Elements.Book3

/-- Two circles that touch one another do not have the same center. -/
theorem proposition_6 : ∀ (c f : Point) (α β : Circle),
  α.touchesCircleAt β c ∧ f.isCentre α → ¬(f.isCentre β) :=
by
  euclid_intros
  -- if possible, let F be the center of both; join FC, and draw FEB at random
  euclid_apply (distinct_points f) as x
  euclid_apply (line_from_points f x) as FB
  euclid_apply (intersection_circle_line_extending_points α FB f x) as b
  euclid_apply (intersection_circle_line_extending_points β FB f x) as e
  -- FC = FB and FC = FE, so FE = FB
  euclid_apply (point_on_circle_onlyif f c b α)
  euclid_apply (point_on_circle_onlyif f c e β)
  -- Missed by Euclid: E ≠ B is read off the figure. With FE = FB the circles have one
  -- center and one radius, so they are the same circle.
  euclid_apply (equal_circles f b e α β)
  euclid_finish

end Elements.Book3
