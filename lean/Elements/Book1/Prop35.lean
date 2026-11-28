import SystemE
import Elements.Book1.Prop04
import Elements.Book1.Prop29
import Elements.Book1.Prop33
import Elements.Book1.Prop34


namespace Elements.Book1

-- The case where E falls between D and F; G, where BE meets DC, is given.
-- proposition_35' covers every position of E and F.
theorem proposition_35 : ∀ (a b c d e f g : Point) (AF BC AB CD EB FC : Line),
  formParallelogram a d b c AF BC AB CD ∧ formParallelogram e f b c AF BC EB FC ∧
  between a d e ∧ between d e f ∧ g.onLine CD ∧ g.onLine EB →
  ▱ b:c:a:d = ▱ e:f:b:c :=
by
  euclid_intros
  euclid_apply (proposition_34' a d b c AF BC AB CD)
  euclid_apply (proposition_34' e f b c AF BC EB FC)
  euclid_assert (|(a─d)| = |(e─f)|)
  euclid_assert (|(a─e)| = |(d─f)|)
  euclid_apply (proposition_29_exterior c b f d a CD AB AF)
  euclid_apply (proposition_4 a e b d f c AF EB AB AF FC CD)
  euclid_finish

-- Prop. 35 when F falls beyond D: both parallelograms equal a third, PBCQ, beyond them.
theorem proposition_35_beyond : ∀ (a b c d e f : Point) (AF BC AB CD EB FC : Line),
  formParallelogram a d b c AF BC AB CD ∧ formParallelogram e f b c AF BC EB FC ∧ between a d f →
  ▱ b:c:a:d = ▱ e:f:b:c :=
by
  euclid_intros
  euclid_apply (extend_point AF d f) as p
  euclid_apply (extend_point_longer AF f p (b─c)) as q'
  euclid_apply (proposition_3 p q' b c AF BC) as q
  euclid_apply (line_from_points p b) as PB
  euclid_apply (line_from_points q c) as QC
  euclid_assert p.sameSide b QC
  euclid_apply (proposition_33 p q b c AF BC PB QC)
  euclid_apply (intersection_lines CD PB) as g
  euclid_apply (intersection_lines FC PB) as h
  euclid_apply (proposition_35 a b c d p q g AF BC AB CD PB QC)
  euclid_apply (proposition_35 e b c f p q h AF BC EB FC PB QC)
  euclid_finish

-- Prop. 35 in general, wherever E and F fall on AF.
-- Two parallelograms on BC, with AD and EF on one line: if F is not beyond D, D is beyond F.
theorem proposition_35_order : ∀ (a b c d e f : Point) (AF BC CD FC : Line),
  distinctPointsOnLine a d AF ∧ distinctPointsOnLine e f AF ∧ distinctPointsOnLine b c BC ∧
  distinctPointsOnLine d c CD ∧ distinctPointsOnLine f c FC ∧ ¬(AF.intersectsLine BC) ∧
  a.sameSide b CD ∧ e.sameSide b FC ∧ ¬(between a d f) ∧ f ≠ d →
  between e f d :=
by
  euclid_intros
  have : ¬(d.onLine BC) := by euclid_finish
  have : ¬(f.onLine BC) := by euclid_finish
  have : d.sameSide f BC := by
    by_contra h
    exact ‹¬AF.intersectsLine BC› (intersection_symm _ _
      (intersection_lines_opposing d f BC AF ⟨⟨‹_›, ‹_›, h⟩, ‹_›, ‹_›⟩))
  have hfb : f.sameSide b CD := by
    by_cases (f = a)
    · euclid_finish
    · by_contra
      euclid_apply (pasch_4 a d f CD AF)
      euclid_finish
  by_contra
  have : d.sameSide b FC := by
    by_cases (e = d)
    · euclid_finish
    · by_contra
      euclid_apply (pasch_4 e f d FC AF)
      euclid_finish
  have : b.sameSide d FC := same_side_symm d b FC ‹_›
  exact triple_incidence_1 BC CD FC c b d f ⟨‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›⟩
    (same_side_symm f b CD hfb)

theorem proposition_35' : ∀ (a b c d e f : Point) (AF BC AB CD EB FC : Line),
  formParallelogram a d b c AF BC AB CD ∧ formParallelogram e f b c AF BC EB FC →
  ▱ b:c:a:d = ▱ e:f:b:c :=
by
  euclid_intros
  by_cases (between a d f)
  · euclid_apply (proposition_35_beyond a b c d e f AF BC AB CD EB FC)
    euclid_finish
  · by_cases (f = d)
    · -- Omitted by Euclid: the parallelograms are the same.
      euclid_assert e = a
      euclid_apply (parallelogram_area a d b c AF BC AB CD)
      euclid_finish
    · -- Omitted by Euclid: D falls beyond F.
      euclid_apply (proposition_35_order a b c d e f AF BC CD FC)
      euclid_apply (proposition_35_beyond e b c f a d AF BC EB FC AB CD)
      euclid_finish

end Elements.Book1
