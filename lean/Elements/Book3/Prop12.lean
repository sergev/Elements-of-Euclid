import SystemE
import Elements.Book1.Prop20
import Elements.Book3.Prop06

namespace Elements.Book3

/-- Circles touching externally: no point of one is inside the other. -/
theorem proposition_12_lemma : ∀ (a c f g : Point) (FG : Line) (α β : Circle),
  α.touchesExternallyAt β a ∧ f.isCentre α ∧ g.isCentre β ∧ distinctPointsOnLine f g FG ∧
  c.onCircle α ∧ c.insideCircle β → False :=
by
  euclid_intros
  euclid_apply (‹∀ x : Point, x.insideCircle α → ¬x.insideCircle β› f)
  by_cases (f.onCircle β)
  · -- a point P on FG near F is inside both
    euclid_apply (exists_distinct_point_on_circle α f) as r
    euclid_apply (point_between_points_shorter_than FG f g (f─r)) as p
    euclid_apply (point_in_circle_if f r p α)
    euclid_apply (‹∀ x : Point, x.insideCircle α → ¬x.insideCircle β› p)
    euclid_finish
  · -- F is outside β, and C on α inside it: the circles cut
    euclid_apply (intersection_circle_circle_1 c f α β)
    euclid_finish

/-- Circles touching externally at `A`: the line `FG` joining the centers goes through `A`. -/
theorem proposition_12 : ∀ (a f g : Point) (FG : Line) (α β : Circle),
  α.touchesExternallyAt β a ∧ f.isCentre α ∧ g.isCentre β ∧ f.onLine FG ∧ g.onLine FG →
  a.onLine FG :=
by
  euclid_intros
  -- Missed by Euclid: F and G are distinct [Prop. 3.6].
  euclid_apply (proposition_6 a f α β)
  by_contra
  -- if possible, let it go like FCDG, and let AF, AG be joined
  euclid_apply (line_from_points a f) as AF
  euclid_apply (line_from_points a g) as AG
  -- FA and AG are greater than FG [Prop. 1.20]
  euclid_apply (Elements.Book1.proposition_20 a f g AF FG AG)
  -- Missed by Euclid: G is not inside α, so FG meets α at C, with FC = FA; then GC is
  -- less than GA = GD, and C is inside β.
  have : ¬(g.insideCircle α) := fun h =>
    ‹∀ x : Point, x.insideCircle α → ¬x.insideCircle β› g h (center_inside_circle g β ‹_›)
  by_cases (g.onCircle α)
  · euclid_apply (proposition_12_lemma a g f g FG α β)
    euclid_finish
  · euclid_apply (intersection_circle_line_between_points α FG f g) as c
    euclid_apply (point_on_circle_onlyif f a c α)
    euclid_apply (between_if f c g)
    euclid_apply (point_in_circle_if g a c β)
    euclid_apply (proposition_12_lemma a c f g FG α β)
    euclid_finish

end Elements.Book3
