import SystemE
import Elements.Book1.Prop23
import Elements.Book3.Prop26

namespace Elements.Book3

/--
Euclid's argument in Prop. 3.27: if `BGC` is greater than `EHF`, then `BGK`, made equal to
`EHF` [Prop. 1.23], stands on a circumference `BK` equal to `EF` [Prop. 3.26], and so to
`BC`, the lesser to the greater.
-/
theorem proposition_27_lemma : ∀ (b c e f g h : Point) (BC EF : Line) (α β : Circle),
  g.isCentre α ∧ h.isCentre β ∧ b.onCircle α ∧ c.onCircle α ∧ e.onCircle β ∧
  f.onCircle β ∧ |(g─b)| = |(h─e)| ∧ distinctPointsOnLine b c BC ∧
  distinctPointsOnLine e f EF ∧ ¬(g.onLine BC) ∧ ¬(h.onLine EF) ∧
  α.arc b c g = β.arc e f h ∧ ∠ e:h:f < ∠ b:g:c → False :=
by
  euclid_intros
  euclid_apply (line_from_points g b) as GB
  euclid_apply (line_from_points g c) as GC
  euclid_apply (line_from_points h e) as HE
  euclid_apply (line_from_points h f) as HF
  -- the angle BGK equal to EHF [Prop. 1.23]
  euclid_apply (Elements.Book1.proposition_23_side g b h e f c GB HE HF) as k'
  euclid_apply (line_from_points g k') as GK
  -- Missed by Euclid: GK is within the angle BGC, and cuts BC at P and the circle at K
  -- beyond P, on the circumference BC.
  by_cases (k'.sameSide b GC)
  · euclid_apply (intersection_lines_opposing b c GK BC)
    euclid_apply (intersection_lines GK BC) as p
    euclid_apply (circle_points_between b c p α)
    euclid_apply (extend_point GK k' g) as x
    euclid_apply (intersection_circle_line_extending_points α GK g x) as k
    euclid_apply (point_in_circle_onlyif g b p α)
    euclid_apply (point_on_circle_onlyif g b k α)
    euclid_assert between g p k
    euclid_apply (equal_angles g b b k' k GB GK)
    -- the circumference BK is equal to EF [Prop. 3.26], and so to BC
    euclid_apply (line_from_points b k) as BK
    euclid_apply (line_from_points k c) as KC
    euclid_apply (proposition_26' b k e f g h BK EF α β)
    -- but BK is less than BC
    euclid_apply (arc_add b c k g BC α)
    euclid_apply (arc_side b k c g BK α)
    euclid_apply (arc_pos k c b KC α)
    euclid_finish
  · exfalso
    have : ¬(k'.onLine GC) := by
      intro
      euclid_apply (equal_angles g b b c k' GB GC)
      euclid_finish
    euclid_apply (sum_angles_onlyif g b k' c GB GK)
    euclid_finish

/-- In equal circles, angles `BGC`, `EHF` at the centers on equal circumferences are
equal. -/
theorem proposition_27' : ∀ (b c e f g h : Point) (BC EF : Line) (α β : Circle),
  g.isCentre α ∧ h.isCentre β ∧ b.onCircle α ∧ c.onCircle α ∧ e.onCircle β ∧
  f.onCircle β ∧ |(g─b)| = |(h─e)| ∧ distinctPointsOnLine b c BC ∧
  distinctPointsOnLine e f EF ∧ ¬(g.onLine BC) ∧ ¬(h.onLine EF) ∧
  α.arc b c g = β.arc e f h → ∠ b:g:c = ∠ e:h:f :=
by
  euclid_intros
  -- if BGC is unequal to EHF, one of them is greater
  rcases lt_trichotomy (∠ e:h:f) (∠ b:g:c) with _ | _ | _
  · exfalso
    euclid_apply (proposition_27_lemma b c e f g h BC EF α β)
    euclid_finish
  · euclid_finish
  · exfalso
    euclid_apply (proposition_27_lemma e f b c h g EF BC β α)
    euclid_finish

/--
In equal circles, angles `BAC`, `EDF` at the circumference on equal circumferences are
equal. As in Euclid's figure, the centers are within the angles (the circumferences are
less than semicircles); the statement assumes it.
-/
theorem proposition_27 : ∀ (a b c d e f g h : Point) (BC EF : Line) (α β : Circle),
  g.isCentre α ∧ h.isCentre β ∧ a.onCircle α ∧ b.onCircle α ∧ c.onCircle α ∧
  d.onCircle β ∧ e.onCircle β ∧ f.onCircle β ∧ |(g─b)| = |(h─e)| ∧
  distinctPointsOnLine b c BC ∧ distinctPointsOnLine e f EF ∧
  g.sameSide a BC ∧ h.sameSide d EF ∧ α.arc b c a = β.arc e f d → ∠ b:a:c = ∠ e:d:f :=
by
  euclid_intros
  euclid_apply (arc_side b c a g BC α)
  euclid_apply (arc_side e f d h EF β)
  euclid_apply (proposition_27' b c e f g h BC EF α β)
  -- the angle at A is half BGC, and that at D half EHF [Prop. 3.20]
  euclid_apply (proposition_20 a b c g BC α)
  euclid_apply (proposition_20 d e f h EF β)
  euclid_finish

end Elements.Book3
