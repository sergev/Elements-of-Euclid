import SystemE
import Elements.Book1.Prop23
import Elements.Book3.Prop26

namespace Elements.Book3

/--
`x` within the angle `ugy` at the center: the angle `ugy` is made of `ugx`, `xgy`, and
the circumference `uy` of `ux`, `xy`. `x` is on `y`'s side of `GU`, and `GX` separates
`u` from `y`.
-/
theorem center_add : ∀ (g u x y : Point) (GU GX : Line) (α : Circle),
  g.isCentre α ∧ u.onCircle α ∧ x.onCircle α ∧ y.onCircle α ∧
  distinctPointsOnLine g u GU ∧ distinctPointsOnLine g x GX ∧ x.sameSide y GU ∧
  u.opposingSides y GX →
  ∠ u:g:y = ∠ u:g:x + ∠ x:g:y ∧ α.arc u y g = α.arc u x g + α.arc x y g :=
by
  euclid_intros
  euclid_apply (line_from_points u y) as UY
  euclid_apply (line_from_points g y) as GY
  euclid_apply (line_from_points u x) as UX
  euclid_apply (line_from_points x y) as XY
  -- `GX` cuts `UY` at `p`, inside the circle; `x` is beyond `p`
  euclid_apply (intersection_lines_opposing u y GX UY)
  euclid_apply (intersection_lines GX UY) as p
  euclid_apply (circle_points_between u y p α)
  euclid_apply (point_in_circle_onlyif g u p α)
  euclid_apply (point_on_circle_onlyif g u x α)
  euclid_assert p.sameSide x GU
  euclid_assert p ≠ g
  euclid_assert p ≠ x
  have : between g p x := by
    rcases between_points g p x GX (by euclid_finish) with _ | _ | _
    · assumption
    · exfalso; euclid_finish
    · exfalso
      euclid_apply (between_if g x p)
      euclid_finish
  euclid_apply (sum_angles_onlyif g u y x GU GY)
  euclid_apply (arc_add u y x g UY α)
  euclid_apply (arc_side u x y g UX α)
  euclid_apply (arc_side x y u g XY α)
  euclid_finish

/--
At the center `g` of `α`, on `GX`, on the side of `t`, an angle `xgy` equal to the angle
`bhc` at the center of an equal circle `β` [Prop. 1.23], with `y` on `α`: it stands on a
circumference equal to `bc` [Prop. 3.26].
-/
theorem lay_off : ∀ (b c g h x t : Point) (BC GX : Line) (α β : Circle),
  h.isCentre β ∧ b.onCircle β ∧ c.onCircle β ∧ distinctPointsOnLine b c BC ∧
  ¬(h.onLine BC) ∧ g.isCentre α ∧ x.onCircle α ∧ |(g─x)| = |(h─b)| ∧
  distinctPointsOnLine g x GX ∧ ¬(t.onLine GX) →
  ∃ y : Point, y.onCircle α ∧ y.sameSide t GX ∧ ∠ x:g:y = ∠ b:h:c ∧
  α.arc x y g = β.arc b c h :=
by
  euclid_intros
  euclid_apply (line_from_points h b) as HB
  euclid_apply (line_from_points h c) as HC
  euclid_apply (Elements.Book1.proposition_23_side g x h b c t GX HB HC) as k
  euclid_apply (line_from_points g k) as GK
  euclid_apply (extend_point GK k g) as w
  euclid_apply (intersection_circle_line_extending_points α GK g w) as y
  euclid_apply (equal_angles g x x k y GX GK)
  euclid_apply (line_from_points x y) as XY
  euclid_apply (proposition_26' x y b c g h XY BC α β)
  use y
  euclid_finish

/--
Euclid's argument in Prop. 3.27: in equal circles, if `BGC` is greater than `EHF`, then
`BGK`, made equal to `EHF` [Prop. 1.23], stands on a circumference `BK` equal to `EF`
[Prop. 3.26], and `BK` is less than `BC`: the greater angle at the center stands on the
greater circumference.
-/
theorem proposition_27_lemma : ∀ (b c e f g h : Point) (BC EF : Line) (α β : Circle),
  g.isCentre α ∧ h.isCentre β ∧ b.onCircle α ∧ c.onCircle α ∧ e.onCircle β ∧
  f.onCircle β ∧ |(g─b)| = |(h─e)| ∧ distinctPointsOnLine b c BC ∧
  distinctPointsOnLine e f EF ∧ ¬(g.onLine BC) ∧ ¬(h.onLine EF) ∧
  ∠ e:h:f < ∠ b:g:c → β.arc e f h < α.arc b c g :=
by
  euclid_intros
  euclid_apply (line_from_points g b) as GB
  -- `BGK` equal to `EHF`, on the side of `C`
  euclid_apply (lay_off e f g h b c EF GB α β) as k
  euclid_apply (line_from_points g k) as GK
  -- Missed by Euclid: `GK` is within the angle `BGC`
  have : b.opposingSides c GK := by
    by_cases (c.onLine GK)
    · exfalso
      euclid_apply (equal_angles g b b k c GB GK)
      euclid_finish
    · by_cases (b.sameSide c GK)
      · exfalso
        euclid_apply (sum_angles_onlyif g b k c GB GK)
        euclid_finish
      · euclid_finish
  euclid_apply (center_add g b k c GB GK α)
  euclid_apply (line_from_points k c) as KC
  euclid_apply (arc_pos k c g KC α)
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
