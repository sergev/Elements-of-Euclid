import SystemE
import Elements.Book1.Prop04
import Elements.Book1.Prop10
import Elements.Book3.Axioms
import Elements.Book3.Prop20

namespace Elements.Book3

/--
In equal circles, equal angles `BAC`, `EDF` at the circumference stand on equal chords:
the angles at the centers are equal [Prop. 3.20], and so are the bases [Prop. 1.4].
Missed by Euclid: he has the angles at the centers given equal as well.
-/
theorem proposition_26_chord : ∀ (a b c d e f g h : Point) (BC EF : Line) (α β : Circle),
  g.isCentre α ∧ h.isCentre β ∧ a.onCircle α ∧ b.onCircle α ∧ c.onCircle α ∧
  d.onCircle β ∧ e.onCircle β ∧ f.onCircle β ∧ |(g─b)| = |(h─e)| ∧
  distinctPointsOnLine b c BC ∧ distinctPointsOnLine e f EF ∧ ¬(a.onLine BC) ∧
  ¬(d.onLine EF) ∧ ∠ b:a:c = ∠ e:d:f → |(b─c)| = |(e─f)| :=
by
  euclid_intros
  euclid_apply (point_on_circle_onlyif g b c α)
  euclid_apply (point_on_circle_onlyif h e f β)
  euclid_apply (angle_range (Angle.ofPoints b g c))
  euclid_apply (angle_range (Angle.ofPoints e h f))
  by_cases (g.onLine BC)
  · euclid_apply (proposition_20'' a b c g BC α)
    by_cases (h.onLine EF)
    · -- both chords are diameters
      euclid_apply (circle_line_intersections g b c BC α)
      euclid_apply (circle_line_intersections h e f EF β)
      euclid_apply (between_if b g c)
      euclid_apply (between_if e h f)
      euclid_finish
    · exfalso
      by_cases (h.sameSide d EF)
      · euclid_apply (proposition_20 d e f h EF β)
        euclid_apply (flat_angle_if e h f)
        euclid_finish
      · euclid_apply (proposition_20' d e f h EF β)
        euclid_apply (flat_angle_if e h f)
        euclid_finish
  · euclid_apply (line_from_points g b) as GB
    euclid_apply (line_from_points g c) as GC
    euclid_apply (line_from_points h e) as HE
    euclid_apply (line_from_points h f) as HF
    by_cases (g.sameSide a BC)
    · euclid_apply (proposition_20 a b c g BC α)
      by_cases (h.onLine EF)
      · exfalso
        euclid_apply (proposition_20'' d e f h EF β)
        euclid_apply (flat_angle_if b g c)
        euclid_finish
      · by_cases (h.sameSide d EF)
        · euclid_apply (proposition_20 d e f h EF β)
          euclid_apply (Elements.Book1.proposition_4 g b c h e f GB BC GC HE EF HF)
          euclid_finish
        · exfalso
          euclid_apply (proposition_20' d e f h EF β)
          euclid_apply (flat_angle_if b g c)
          euclid_finish
    · euclid_apply (proposition_20' a b c g BC α)
      by_cases (h.onLine EF)
      · exfalso
        euclid_apply (proposition_20'' d e f h EF β)
        euclid_apply (flat_angle_if b g c)
        euclid_finish
      · by_cases (h.sameSide d EF)
        · exfalso
          euclid_apply (proposition_20 d e f h EF β)
          euclid_apply (flat_angle_if e h f)
          euclid_finish
        · euclid_apply (proposition_20' d e f h EF β)
          euclid_apply (Elements.Book1.proposition_4 g b c h e f GB BC GC HE EF HF)
          euclid_finish

/--
In equal circles, equal angles `BAC`, `EDF` at the circumference stand on equal
circumferences `BC`, `EF` (away from `A`, `D`).
-/
theorem proposition_26 : ∀ (a b c d e f g h : Point) (BC EF : Line) (α β : Circle),
  g.isCentre α ∧ h.isCentre β ∧ a.onCircle α ∧ b.onCircle α ∧ c.onCircle α ∧
  d.onCircle β ∧ e.onCircle β ∧ f.onCircle β ∧ |(g─b)| = |(h─e)| ∧
  distinctPointsOnLine b c BC ∧ distinctPointsOnLine e f EF ∧ ¬(a.onLine BC) ∧
  ¬(d.onLine EF) ∧ ∠ b:a:c = ∠ e:d:f → α.arc b c a = β.arc e f d :=
by
  euclid_intros
  -- the bases BC, EF are equal [Prop. 1.4]
  euclid_apply (proposition_26_chord a b c d e f g h BC EF α β)
  -- the segments BAC, EDF are similar [Def. 3.11], on equal straight lines, so equal
  -- [Prop. 3.24], and so are their circumferences
  euclid_apply (exists_point_opposite BC a) as a'
  euclid_apply (exists_point_opposite EF d) as d'
  euclid_apply (arc_eq_of_segments b c e f g h a d a' d' BC EF α β)
  -- the whole circles are equal; the remaining circumferences BC, EF are equal
  euclid_apply (circumference_eq g b h e α β)
  euclid_apply (arc_whole b c a a' BC α)
  euclid_apply (arc_whole e f d d' EF β)
  euclid_finish

/-- In equal circles, equal angles `BGC`, `EHF` at the centers stand on equal
circumferences. -/
theorem proposition_26' : ∀ (b c e f g h : Point) (BC EF : Line) (α β : Circle),
  g.isCentre α ∧ h.isCentre β ∧ b.onCircle α ∧ c.onCircle α ∧ e.onCircle β ∧
  f.onCircle β ∧ |(g─b)| = |(h─e)| ∧ distinctPointsOnLine b c BC ∧
  distinctPointsOnLine e f EF ∧ ¬(g.onLine BC) ∧ ¬(h.onLine EF) ∧
  ∠ b:g:c = ∠ e:h:f → α.arc b c g = β.arc e f h :=
by
  euclid_intros
  -- Missed by Euclid: angles BAC, EDF at the circumferences, with A, D on the side of
  -- the centers, are halves of those at the centers [Prop. 3.20], and so equal
  euclid_apply (Elements.Book1.proposition_10 b c BC) as m
  euclid_apply (line_from_points m g) as MG
  euclid_apply (intersection_circle_line_extending_points α MG g m) as a
  euclid_apply (Elements.Book1.proposition_10 e f EF) as n
  euclid_apply (line_from_points n h) as NH
  euclid_apply (intersection_circle_line_extending_points β NH h n) as d
  euclid_apply (proposition_20 a b c g BC α)
  euclid_apply (proposition_20 d e f h EF β)
  euclid_apply (proposition_26 a b c d e f g h BC EF α β)
  euclid_apply (arc_side b c a g BC α)
  euclid_apply (arc_side e f d h EF β)
  euclid_finish

end Elements.Book3
